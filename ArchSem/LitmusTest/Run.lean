-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

import ArchSem.LitmusTest.Defs
import ArchSem.TerminatingModel
import Sail.ArchSem

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest.Run

variable [Arch] [ArchExtra]

/--
Convert list of final states to a string for debugging.
-/
def finalStatesToString (states : List (ArchState nThreads)) : String :=
  let regMapToString (regs : RegisterMap) : String :=
    "[" ++ ", ".intercalate (regs.toList.map (fun pair => s!"{reprStr pair.fst}={reprStr pair.snd}")) ++ "]"
  let memMapToString (mem : MemoryMap) : String :=
    "[" ++ ", ".intercalate (mem.toList.map (fun pair => s!"{pair.fst.toHex}={pair.snd.toHex}")) ++ "]"
  let archStateToString (state : ArchState nThreads) : String :=
    let regsStr := "[" ++ ", ".intercalate (state.regs.toList.map regMapToString) ++ "]"
    let memStr := memMapToString state.memory
    s!"regs={regsStr}, mem={memStr}"
  "[\n" ++ "\n".intercalate (states.map archStateToString) ++ "]\n"

/--
`ArchTestRepr` is a `TestRepr` that has been specialised to a particular architecture
with `ArchTestRepr.ofTestRepr`.
-/
structure ArchTestRepr [ArchExtra] (nThreads : Nat) where
  initialState : ArchState nThreads
  terminationCondition : TerminationCondition nThreads
  /-- Pass a list of final states to get test result. Encodes final conditions. -/
  checkFinalConditions : List (ArchState nThreads) → Except String LitmusTestResult

def ArchTestRepr.ofTestRepr [ArchExtra] (test : TestRepr)
    : Except String (ArchTestRepr test.registers.length) := do

  -- Helper function for register map conversion.
  let tableToRegMap (l : List (String × RegValGen)) : Except String RegisterMap :=
    l.foldlM (fun regs (s, rv) => do
      let reg : Arch.register ← ArchExtra.register_of_string s
      let val : Arch.register_type reg ← ArchExtra.register_type_of_gen reg rv
      pure (regs.insert reg val)
    ) RegisterMap.empty

  -- Convert TestRepr lists into Vectors of same length.
  let nThreads : Nat := test.registers.length
  let testRegsVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨test.registers.toArray, rfl⟩
  if h : test.termCond.length != nThreads then
    Except.error "A termination condition must be supplied for every thread" else
  let testTermCondVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨test.termCond.toArray, by simp at h ; exact h⟩

  -- Convert to ArchState types.
  let memory : MemoryMap := test.memory.foldl MemoryBlock.insertIntoMemoryMap MemoryMap.empty
  let addressSpace : Arch.addr_space := default
  let regs : Vector RegisterMap nThreads ← testRegsVec.mapM tableToRegMap
  let initialState : ArchState nThreads := { memory, addressSpace, regs}

  -- Convert termination condition.
  let termCondRegs : Vector RegisterMap nThreads ← testTermCondVec.mapM tableToRegMap
  let terminationCondition : TerminationCondition nThreads :=
    fun tid regs => termCondRegs[tid].all (fun r v => regs.get? r == some v)

  -- Convert final condition check.
  let checkFinalMemoryCondition (archState : ArchState nThreads) (cond : FinalMemoryCondition)
      : Except String Bool :=
    let addr : Address := BitVec.ofNat Arch.addr_size cond.addr
    let word : BitVec (8 * cond.size) := archState.memory.read cond.size addr
    match cond.condition with
    | .memEq n => .ok (word.toNat == n)
    | .memNe n => .ok (word.toNat != n)
  let checkFinalThreadRegisterCondition (archState : ArchState nThreads) (tid : Tid)
      (pair : String × FinalRegisterCondition) : Except String Bool := Id.run do
    let (regStr,cond) := pair
    -- Is tid out of range.
    if h : tid >= nThreads then .error s!"Thread id out of range ({tid} >= {nThreads})" else
    let tid : Fin nThreads := ⟨tid, by simp at h ; exact h⟩
    let reg : Arch.register ← match ArchExtra.register_of_string regStr with
      | .ok reg => reg
      | .error msg => return .error msg
    let valGen : RegValGen := match cond with
      | .regEq rv | .regNe rv => rv
    let val : Arch.register_type reg ← match ArchExtra.register_type_of_gen reg valGen with
      | .ok val => val
      | .error msg => return .error msg
    let trueVal : Arch.register_type reg ← match archState.regs[tid].get? reg with
      | .some val => pure val
      | .none => return .error s!"Register '{reprStr reg}' undefined in final state but checked by final condition."
    match cond with
      | .regEq _ => .ok (val == trueVal)
      | .regNe _ => .ok (val != trueVal)
  let checkFinalThreadCondition (archState : ArchState nThreads) (cond : FinalThreadCondition)
      : Except String Bool :=
    cond.regConditions.allM (checkFinalThreadRegisterCondition archState cond.tid)
  let checkFinalThreadConditions
      (archState : ArchState nThreads)
      (threadConditions : List FinalThreadCondition)
      : Except String Bool :=
    threadConditions.allM (checkFinalThreadCondition archState)
  let checkFinalMemoryConditions
      (archState : ArchState nThreads)
      (memoryConditions : List FinalMemoryCondition)
      : Except String Bool :=
    memoryConditions.allM (checkFinalMemoryCondition archState)
  let checkFinalConditions (finalStates : List (ArchState nThreads)) : Except String LitmusTestResult := do
    let (observables, unobservables)
        : (List (List FinalThreadCondition × List FinalMemoryCondition))
        × (List (List FinalThreadCondition × List FinalMemoryCondition))
      := test.finalConditions.foldl (fun (obs, unobs) cond => match cond with
        | .observable threadConds memConds => ((threadConds, memConds) :: obs, unobs)
        | .unobservable threadConds memConds => (obs, (threadConds, memConds) :: unobs)
        ) ([], [])
    let checkCondExists (cond : (List FinalThreadCondition × List FinalMemoryCondition))
        : Except String Bool :=
      finalStates.anyM (fun archState => do
        let threadCondExists ← checkFinalThreadConditions archState cond.fst
        let memoryCondExists ← checkFinalMemoryConditions archState cond.snd
        return (threadCondExists && memoryCondExists))
    if !(← observables.allM checkCondExists) then
      return .forbidden s!"Not all observable conditions observed."
    if (← unobservables.anyM checkCondExists) then
      return .forbidden s!"An unobservable condition was observed."
    return .allowed

  -- Return ArchTestRepr.
  pure { initialState, terminationCondition, checkFinalConditions}

/--
Run a litmus test using the given computational model and
reutrn the result (allowed/forbidden).
-/
def runLitmusTest [ArchExtra]
    (model : ComputationalTerminatingModel) (litmusTest : TestRepr)
    : Except String LitmusTestResult := do
  let nThreads : Nat := litmusTest.registers.length
  let archTest : ArchTestRepr nThreads ← ArchTestRepr.ofTestRepr litmusTest
  let output := model nThreads archTest.terminationCondition archTest.initialState
  -- Finset.imageMap would make this easier.
  let errors := output.filterMap (fun
    | .finalState _ _ => .none
    | .flagged f => .some s!"Unexpected flagged output {f}"
    | .error msg => .some msg)
  if !errors.isEmpty then
    Except.error ("errors:" ++ "\n".intercalate errors)
  let archStates := output.filterMap (fun
    | .finalState archState _ => .some archState
    | .flagged _ => .none
    | .error _ => .none
    )
  archTest.checkFinalConditions archStates

end ArchSem.LitmusTest.Run

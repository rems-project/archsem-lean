import ArchSem.LitmusTest.Defs
import ArchSem.TerminatingModel
import Sail.ArchSem
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest.Run

-- TODO: print more concisely.
def outcomesToString [ArchExtra] (states : Finset (ArchState nThreads)) : String :=
  let regMapToString (regs : RegisterMap) : String :=
    "[" ++ ", ".intercalate (regs.toList.map (fun pair => s!"{reprStr pair.fst}={reprStr pair.snd}")) ++ "]"
  let memMapToString (mem : MemoryMap) : String :=
    "[" ++ ", ".intercalate (mem.toList.map (fun pair => s!"{pair.fst.toHex}={pair.snd.toHex}")) ++ "]"
  let archStateToString (state : ArchState nThreads) : String :=
    let regsStr := "[" ++ ", ".intercalate (state.regs.toList.map regMapToString) ++ "]"
    let memStr := memMapToString state.memory
    s!"regs={regsStr}, mem={memStr}"
  "[\n" ++ "\n".intercalate (states.image archStateToString).sort ++ "]\n"

structure ArchTestRepr [ArchExtra] (nThreads : Nat) where
  initialState : ArchState nThreads
  terminationCondition : TerminationCondition nThreads
  checkFinalConditions : Finset (ArchState nThreads) → Except String Unit

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
      : Bool :=
    let addr : Address := BitVec.ofNat Arch.addr_size cond.addr
    let word : BitVec (8 * cond.size) := archState.memory.read cond.size addr
    match cond.condition with
    | .memEq n => word.toNat == n
    | .memNe n => word.toNat != n
  let checkFinalThreadRegisterCondition (archState : ArchState nThreads) (tid : Tid)
      (pair : String × FinalRegisterCondition) : Bool := Id.run do
    let (regStr,cond) := pair
    -- Is tid out of range.
    if h : tid >= nThreads then false else
    let tid : Fin nThreads := ⟨tid, by simp at h ; exact h⟩
    let reg : Arch.register ← match ArchExtra.register_of_string regStr with
      | .ok reg => reg
      | .error _e => return false -- TODO: propigate error message.
    let valGen : RegValGen := match cond with
      | .regEq rv | .regNe rv => rv
    let val : Arch.register_type reg ← match ArchExtra.register_type_of_gen reg valGen with
      | .ok val => val
      | .error _e => return false -- TODO: propigate error message.
    let trueVal : Arch.register_type reg ← match archState.regs[tid].get? reg with
      | .some val => pure val
      | .none => return false -- TODO: propigate error message (reg not set).
    match cond with
      | .regEq _ => val == trueVal
      | .regNe _ => val != trueVal
  let checkFinalThreadCondition (archState : ArchState nThreads) (cond : FinalThreadCondition)
      : Bool :=
    cond.regConditions.all (checkFinalThreadRegisterCondition archState cond.tid)
  let checkFinalThreadConditions
      (archState : ArchState nThreads)
      (threadConditions : List FinalThreadCondition)
      : Bool :=
    threadConditions.all (checkFinalThreadCondition archState)
  let checkFinalMemoryConditions
      (archState : ArchState nThreads)
      (memoryConditions : List FinalMemoryCondition)
      : Bool :=
    memoryConditions.all (checkFinalMemoryCondition archState)
  let checkFinalConditions (finalStates : Finset (ArchState nThreads)) : Except String Unit := do
    let (observables, unobservables)
        : (List (List FinalThreadCondition × List FinalMemoryCondition))
        × (List (List FinalThreadCondition × List FinalMemoryCondition))
      := test.finalConditions.foldl (fun (obs, unobs) cond => match cond with
        | .observable threadConds memConds => ((threadConds, memConds) :: obs, unobs)
        | .unobservable threadConds memConds => (obs, (threadConds, memConds) :: unobs)
        ) ([], [])
    let checkCondExists (cond : (List FinalThreadCondition × List FinalMemoryCondition)) : Bool :=
      decide (∃ archState ∈ finalStates,
        (checkFinalThreadConditions archState cond.fst) ∧
        (checkFinalMemoryConditions archState cond.snd))
    let debugInfo := s!"final states:\n{outcomesToString finalStates}"
    if !(observables.all checkCondExists) then
      Except.error s!"Not all observable conditions observed.\n{debugInfo}"
    if (unobservables.any checkCondExists) then
      Except.error "An unobservable condition was observed.\n{debugInfo}"
    pure ()

  -- Return ArchTestRepr.
  pure { initialState, terminationCondition, checkFinalConditions}

def runLitmusTest [ArchExtra]
    (model : ComputationalTerminatingModel) (litmusTest : TestRepr)
    : Except String Unit := do
  let nThreads : Nat := litmusTest.registers.length
  let archTest : ArchTestRepr nThreads ← ArchTestRepr.ofTestRepr litmusTest
  let output := model nThreads archTest.terminationCondition archTest.initialState
  let archStates := output.filterMap (fun
    | .finalState archState _ => .some archState
    | .flagged f => .none
    | .error msg => .none
    ) (by grind)
  archTest.checkFinalConditions archStates

end ArchSem.LitmusTest.Run

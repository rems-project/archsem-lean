-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.LitmusTest.Defs
import ArchSem.TerminatingModel
import Sail.ArchSem

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest.Run

variable [Arch] [ArchExtra]

/--
Prepare an architecture-specific initial ArchState from a generic TestRepr.
-/
def buildInitialState (testRepr : TestRepr)
    : Except String (ArchState testRepr.registers.length) := do

  -- Helper function for register map conversion.
  let tableToRegMap (l : List (String × RegValGen)) : Except String RegisterMap :=
    l.foldlM (fun regs (s, rv) => do
      let reg : Arch.register ← ArchExtra.register_of_string s
      let val : Arch.register_type reg ← ArchExtra.register_type_of_gen reg rv
      pure (regs.insert reg val)
    ) RegisterMap.empty

  -- Convert TestRepr lists into Vectors of same length.
  let nThreads : Nat := testRepr.registers.length
  let testRegsVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨testRepr.registers.toArray, rfl⟩

  -- Convert to ArchState types.
  let memory : MemoryMap := testRepr.memory.foldl MemoryBlock.insertIntoMemoryMap MemoryMap.empty
  let addressSpace : Arch.addr_space := default
  let regs : Vector RegisterMap nThreads ← testRegsVec.mapM tableToRegMap

  return {memory, addressSpace, regs}

/--
Prepare an architecture-specific termination condition from a
generic TestRepr.
-/
def buildTerminationCondition (testRepr : TestRepr)
    : Except String (TerminationCondition testRepr.registers.length) :=

  -- Convert TestRepr lists into Vectors of same length.
  let nThreads : Nat := testRepr.registers.length
  let testRegsVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨testRepr.registers.toArray, rfl⟩
  if h : testRepr.termCond.length != nThreads then
    Except.error "A termination condition must be supplied for every thread" else
  let testTermCondVec : Vector (List Nat) nThreads :=
    ⟨testRepr.termCond.toArray, by simp at h ; exact h⟩

  return (fun tid regs => testTermCondVec[tid].all (fun breakpoint =>
    match regs.get? ArchExtra.register_pc with
    | .some pc => match ArchExtra.register_to_nat pc with
      | .ok pcNat => pcNat = breakpoint
      | .error _ => false
    | .none => false))

/--
Run a litmus test using the given computational model and
reutrn the final states.
-/
def runLitmusTest [ArchExtra]
    (model : ComputationalTerminatingModel) (testRepr : TestRepr)
    : Except String (List (ArchState testRepr.registers.length)) := do
  let nThreads : Nat := testRepr.registers.length
  let initialState : ArchState nThreads ← buildInitialState testRepr
  let termCond : TerminationCondition nThreads ← buildTerminationCondition testRepr
  let modelOutput := model nThreads termCond initialState
  let errors := modelOutput.filterMap (fun
    | .finalState _ _ => .none
    | .flagged f => .some s!"Unexpected flagged output {f}"
    | .error msg => .some msg)
  if !errors.isEmpty then
    let sortedErrors := errors.toSortedList compare
    Except.error ("errors:" ++ "\n".intercalate sortedErrors)
  let finalStates := modelOutput.filterMap (fun
    | .finalState archState _ => .some archState
    | .flagged _ => .none
    | .error _ => .none
    )
  |>.toSortedList compare
  return finalStates

end ArchSem.LitmusTest.Run

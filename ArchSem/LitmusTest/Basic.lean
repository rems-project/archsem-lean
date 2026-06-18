-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.TerminatingModel
import ArchSem.LitmusTest.Defs
import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSem.LitmusTest.MCompare
import ArchSem.LitmusTest.Config

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open Sail.ArchSem

namespace ArchSem.LitmusTest

variable [Arch] [ArchExtra]

/--
Find the address and size of a memory block pointed to by a symbol.
-/
def symResolve (testRepr : TestRepr) (sym : String)
    : Except String (Nat × Nat) :=
  match testRepr.memory.find? (fun block => block.sym = .some sym) with
  | .some block => return (block.addr, block.step)
  | .none => Except.error s!"Invalid memory symbol {sym}"

/--
We have two string representations of registers: ISLA (X0-X... for ARM)
and ArchSem (R0-R... for ARM).
The archsem litmus test format uses ISLA format for final condition assertion
and the mcompare output must use the ISLA format, elsewhere we use the archsem
format.
In lean datastructures, we use the ISLA format in FinalConditionLoc's and
the ArchSem format everywhere else.

This function converts from ISLA format to ArchSem format using the
litmus test configuration file.
-/
def attemptRegisterRename (config : LitmusTestConfig) (reg : String) : String :=
  match config.registerRenames.get? reg with
  | .some rename => rename
  | .none => reg

/--
Find the value stored at a FinalConditionLoc location in some arch state.
-/
def locResolve (config : LitmusTestConfig) (testRepr : TestRepr) (state : ArchState nThreads)
    : FinalConditionLoc → Except String Nat
  | .reg tid reg => do
    let reg := attemptRegisterRename config reg
    let reg ← ArchExtra.register_of_string reg
    let regMap ← match state.regs[tid]? with
      | .some regMap => pure regMap
      | .none => Except.error "Test tid out of range"
    let regVal ← match regMap.get? reg with
    | .some v => pure v
    | .none => Except.error "Register not in thread"
    ArchExtra.register_to_nat regVal
  | .mem sym => do
    let (addr, size) ← symResolve testRepr sym
    return (state.memory.read size (BitVec.ofNat Arch.addr_size addr)).toNat

/--
Get the locations refered to in a final condition (may output duplicates).
This is used for printing the relevant locations in a state summary.
-/
def getFinalConditionLocs : FinalCondition → List FinalConditionLoc
  | .equalLocLoc l₁ l₂ => [l₁, l₂]
  | .equalLocLiteral l _ => [l]
  | .and cs
  | .or cs => List.flatten (cs.map getFinalConditionLocs)
  | .not c => getFinalConditionLocs c
  | .true
  | .false => []

/--
Summarize an architecture state by the values it has stored in the
locations refered to in the final condition of the test representation.
-/
def finalStateSummary (config : LitmusTestConfig) (testRepr : TestRepr) (state : ArchState nThreads)
    : Except String (List (FinalConditionLoc × Nat)) :=
  let locs : List FinalConditionLoc := getFinalConditionLocs testRepr.finalCondition |>.eraseDups |>.mergeSort
  locs.mapM (fun loc => return (loc, ← locResolve config testRepr state loc ))

/--
Evaluate an arbitrary final condition on a state, using the test representation
to resolve symbol lookups.
-/
def checkFinalCondition' (config : LitmusTestConfig) (testRepr : TestRepr) (state : ArchState nThreads)
    : FinalCondition → Except String Bool
  | .equalLocLoc l₁ l₂ => do
    return (← locResolve config testRepr state l₁) = (← locResolve config testRepr state l₂)
  | .equalLocLiteral l n => do
    return (← locResolve config testRepr state l) = n
  | .and [] => return true
  | .and (cond :: conds) => do
    if !(← checkFinalCondition' config testRepr state cond) then
      return false
    checkFinalCondition' config testRepr state (.and conds)
  | .or [] => return false
  | .or (cond :: conds) => do
    if ← checkFinalCondition' config testRepr state cond then
      return true
    checkFinalCondition' config testRepr state (.or conds)
  | .not cond => do
    return Bool.not (←checkFinalCondition' config testRepr state cond)
  | .true => return true
  | .false => return false

/--
Evaluate a test representations final condition on a state.
-/
def checkFinalCondition (config : LitmusTestConfig) (testRepr : TestRepr) (state : ArchState nThreads)
    : Except String Bool
  := checkFinalCondition' config testRepr state testRepr.finalCondition

/--
Given a test representation and a list of final states, produce a
LitmusTestResult structure containing the detailed litmus test results.
-/
def prepareTestResults (config : LitmusTestConfig) (testRepr : TestRepr) (states : List (ArchState nThreads))
    : Except String LitmusTestResult := do
  let stateSummary ← states.mapM (finalStateSummary config testRepr)
  let (observedStates, notObservedStates) ← match
      List.partitionM (checkFinalCondition config testRepr) states with
    | .ok p => pure p
    | .error msg => Except.error s!"Failed to check final condition: {msg}"
  let observedCount := observedStates.length
  let notObservedCount := notObservedStates.length
  let isOk := match testRepr.kind with
    | .forall => notObservedCount == 0
    | .exists => observedCount > 0
    | .notExists => observedCount == 0
  return {stateSummary, observedCount, notObservedCount, isOk}

/--
Read, parse and run the test in `fname`, using the '.archsem.toml' format.
If the allowed/forbidden outcome disagrees with expectAllowed then throw an error.
This function is useful to use in `#guard` commands for regression tests.
-/
def guardTestFromFile (configFname : System.FilePath) (expectAllowed : Bool)
    (model : ComputationalTerminatingModel) (fname : System.FilePath)
    : IO Unit := do
  let config : LitmusTestConfig ← Config.readConfigFile configFname
  let testRepr : TestRepr ← Parse.readTestFile fname
  let finalStatesOrError := Run.runLitmusTest model testRepr
  match finalStatesOrError with
  | .ok finalStates =>
    let results ← match prepareTestResults config testRepr finalStates with
      | .ok results => pure results
      | .error msg => throw (IO.userError msg)
    let mcompare : String ← match ArchSem.LitmusTest.MCompare.testOutput testRepr results with
      | .ok mcompare => pure mcompare
      | .error msg => throw (IO.userError s!"Failed to prepare mcompare output: {msg}")
    match results.isOk, expectAllowed with
    | true, true => return ()
    | true, false => throw (IO.userError s!"Test allowed but expected forbidden: {fname}\n{mcompare}")
    | false, true => throw (IO.userError s!"Test forbidden but expected allowed: {fname}\n{mcompare}")
    | false, false => return ()
  | .error msg => throw (IO.userError s!"Failed to run test: {msg}")

end ArchSem.LitmusTest

-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.LitmusTest.Defs

/-!
Output litmus test results in a form compatable with mcompare7 from the herd7
suite.
-/

namespace ArchSem.LitmusTest.MCompare

/--
e.g. "1:R0" or "[x]"
-/
def locOutput : FinalConditionLoc → String
  | .reg tid reg => s!"{tid}:{reg}"
  | .mem sym => s!"[{sym}]"

/--
e.g. "1:R0=42 [x]=12"
-/
def stateOutput (state : List (FinalConditionLoc × Nat)) : String :=
  let parts : List String := state.map (fun (loc, val) => s!"{locOutput loc}={val};")
  " ".intercalate parts

/--
e.g. "([x]=2 /\ 1:R1=1)"
-/
def finalConditionOutput : FinalCondition → String
  | .equalLocLoc l₁ l₂ => s!"{locOutput l₁}={locOutput l₂}"
  | .equalLocLiteral l v => s!"{locOutput l}={v}"
  | .and cs => "(" ++ (" /\\ ".intercalate (cs.map finalConditionOutput)) ++ ")"
  | .or cs => "(" ++ (" \\/ ".intercalate (cs.map finalConditionOutput)) ++ ")"
  | .not c => s!"not {finalConditionOutput c}"
  | .true => "true"
  | .false => "false"

/--
Generate an mcompare-compatable representation of a listmus test's results.
-/
def testOutput (test : TestRepr) (result : LitmusTestResult) : Except String String := do
  let states := result.stateSummary
  let observedCount := result.observedCount
  let notObservedCount := result.notObservedCount
  let isOk := result.isOk
  if observedCount + notObservedCount != states.length then
    Except.error s!"Observed counts dont sum to state count {observedCount} + {notObservedCount} != {states.length}"
  if states.length < 1 then
    Except.error s!"Cant output a test with no final states"
  let testName := test.name
  let (testKind, condKind) := match test.kind with
    | .forall => ("Forall", "forall")
    | .exists => ("Allowed", "exists")
    | .notExists => ("Forbidden", "notexists")
  let isOkString := match isOk with
    | true => "Ok"
    | false => "No"
  let finalStateListings : String := "\n".intercalate (states.map stateOutput)
  let finalCond : String := finalConditionOutput test.finalCondition
  let observedString : String :=
    if observedCount == 0 then "Never"
    else if notObservedCount == 0 then "Always"
    else "Sometimes"
  -- TODO: output time in the form `Time {testName} 0.000`
  return s!"\
Test {testName} {testKind}
States {states.length}
{finalStateListings}
{isOkString}
Witnesses
Positive: {observedCount} Negative: {notObservedCount}
Condition {testName} {condKind} {finalCond}
Observation {testName} {observedString} {observedCount} {notObservedCount}

"

end ArchSem.LitmusTest.MCompare

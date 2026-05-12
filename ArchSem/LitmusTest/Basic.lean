-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.TerminatingModel
import ArchSem.LitmusTest.Defs
import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open Sail.ArchSem

namespace ArchSem.LitmusTest

variable [Arch] [ArchExtra]

/-- Read, parse and run the test in `fname`, using the '.archsem.toml' format. -/
def runTestFromFile (model : ComputationalTerminatingModel)
    (fname : System.FilePath)
    : IO (Except String LitmusTestResult) := do
  let test : TestRepr ← Parse.readTestFile fname
  return Run.runLitmusTest model test

/--
Read, parse and run the test in `fname`, using the '.archsem.toml' format.
If the allowed/forbidden outcome disagrees with expectAllowed then throw an error.
This function is useful to use in `#guard` commands for regression tests.
-/
def guardTestFromFile (expectAllowed : Bool)
    (model : ComputationalTerminatingModel) (fname : System.FilePath)
    : IO Unit := do
  let result ← runTestFromFile model fname
  match (result, expectAllowed) with
  | (.ok .allowed, true)
  | (.ok (.forbidden _), false) => return ()
  | (.ok .allowed, false) => throw (IO.userError "Test allowed but expected forbidden")
  | (.ok (.forbidden reason), true) => throw (IO.userError s!"Test forbidden but expected allowed: {reason}")
  | (.error msg, _) => throw (IO.userError s!"Failed to run test: {msg}")

end ArchSem.LitmusTest

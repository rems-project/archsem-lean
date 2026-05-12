-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Cli
import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSem.TerminatingModel
import ArchSemTinyArm.Promising

open ArchSem.LitmusTest
open ArchSem.TerminatingModel (ComputationalTerminatingModel)

def modelFromStr (fuel : Nat) : String → Option ComputationalTerminatingModel
  | "tinyarm-promisefirst" =>
    ArchSemTinyArm.Promising.createPromiseFirstModel
      ArchSemTinyArm.sailTinyArmIsem fuel |> some
  | "tinyarm-promisenaive" =>
    ArchSemTinyArm.Promising.createNaiveModel
      ArchSemTinyArm.sailTinyArmIsem fuel |> some
  | _ => none

def runTests (p : Cli.Parsed) : IO UInt32 := do
  let testFnames : List System.FilePath := p.variableArgsAs! String |>.toList
  let fuel : Nat ← match p.flag? "fuel" |>.bind (Cli.Parsed.Flag.as? · Nat) with
    | .some fuel => pure fuel
    | .none =>
      IO.eprintln "Please specify fuel as a natural number."
      return 1
  let modelStr : String ← match p.flag? "model" |>.bind (Cli.Parsed.Flag.as? · String) with
    | .some str => pure str
    | .none =>
      IO.eprintln "Model unspecified."
      return 1
  let model ← match modelFromStr fuel modelStr with
    | .some m => pure m
    | .none => do
      IO.eprintln s!"Model does not exist: '{modelStr}'"
      return 1
  if testFnames.length == 0 then
    IO.eprintln s!"No tests specified."
    return 1
  let errors : List String ← testFnames.filterMapM (fun fname => do
    (← IO.getStdout).flush
    (← IO.getStderr).flush
    let test ← Parse.readTestFile fname
    let result : Except String LitmusTestResult := Run.runLitmusTest model test
    match result with
    | .ok .allowed =>
      IO.print s!"{test.name}\tOk\n"
      return Option.none
    | .ok (.forbidden _) =>
      IO.print s!"{test.name}\tNo\n"
      return Option.none
    | .error msg =>
      IO.eprintln s!"[{test.name}] Error: {msg}"
      return Option.some msg
  )
  if errors == [] then
    pure 0
  else
    IO.eprintln "At least one test failed."
    pure 1


def litmusTestCmd : Cli.Cmd := `[Cli|
  archsem VIA runTests;
  "Run litmus tests from `.archsem.toml` format."

  FLAGS:
    model : String; "Name of model to use."
    fuel : Nat; ""

  ARGS:
    ...tests : String; "Tests to run of the `.archsem.toml` format."
]

def main (args : List String) : IO UInt32 :=
  litmusTestCmd.validate args

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

-- TODO: terminal colors.
def runTests (p : Cli.Parsed) : IO UInt32 := do
  let testFnames : List System.FilePath := p.variableArgsAs! String |>.toList
  if testFnames.length == 0 then
    IO.eprintln s!"No tests specified."
    return 1
  let fuel : Nat ← match p.flag? "fuel" |>.bind (Cli.Parsed.Flag.as? · Nat) with
    | .some fuel => pure fuel
    | .none =>
      IO.eprintln s!"Fuel must be Nat."
      return 1
  let modelStr : String ← match p.flag? "model" |>.bind (Cli.Parsed.Flag.as? · String) with
    | .some str => pure str
    | .none =>
      IO.eprintln s!"Model unspecified."
      return 1
  let model ← match modelFromStr fuel modelStr with
    | .some m => pure m
    | .none => do
      IO.eprintln s!"Model does not exist: '{modelStr}'"
      return 1
  let tests : List TestRepr ← testFnames.mapM Parse.readTestFile
  let passed : List Bool ← List.zipWithM (fun fname test => do
    let result : Except String Unit := Run.runLitmusTest model test
    match result with
    | .ok () =>
      IO.print s!"[ PASS ] ({fname})\n"
      pure true
    | .error msg =>
      IO.print s!"[ FAIL ] ({fname}):\n{msg}\n"
      pure false
  ) testFnames tests
  if passed.all (· == true) then
    IO.println "✔ All tests passed."
    pure 0
  else
    IO.println "✘ At least one test failed."
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

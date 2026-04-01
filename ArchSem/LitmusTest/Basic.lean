import ArchSem.LitmusTest.Defs
import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSem.TerminatingModel

open ArchSem.TerminatingModel
open ArchSem.LitmusTest

namespace ArchSem.LitmusTest

def runTestFromFile [ArchExtra] (model : ComputationalTerminatingModel)
    (fname : System.FilePath)
    : IO (Except String LitmusTestResult) := do
  let test : TestRepr ← Parse.readTestFile fname
  return Run.runLitmusTest model test

def guardTestFromFile [ArchExtra] (expectAllowed : Bool)
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

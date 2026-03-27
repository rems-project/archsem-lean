import ArchSem.LitmusTest.Defs
import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSem.TerminatingModel

open ArchSem.TerminatingModel
open ArchSem.LitmusTest

namespace ArchSem.LitmusTest

def runTestFromFile [ArchExtra] (fname : System.FilePath)
    (model : ComputationalTerminatingModel) : IO Unit := do
  let test : TestRepr ← Parse.readTestFile fname
  match Run.runLitmusTest model test with
  | .ok () => pure ()
  | .error msg => throw (IO.userError s!"TEST FAILED [{fname.toString}]: {msg}")

end ArchSem.LitmusTest

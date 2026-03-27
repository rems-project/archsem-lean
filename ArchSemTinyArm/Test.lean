import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSemTinyArm.Promising
import ArchSem.TerminatingModel

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open ArchSemTinyArm

namespace ArchSemTinyArm.Test

def fuel : Nat := 10
def naiveModel : ComputationalTerminatingModel :=
  Promising.createNaiveModel sailTinyArmIsem fuel
def promiseFirstModel : ComputationalTerminatingModel :=
  Promising.createPromiseFirstModel sailTinyArmIsem fuel

def runTestFromFile (fname : System.FilePath)
    (model : ComputationalTerminatingModel) : IO Unit := do
  let test : TestRepr ← Parse.readTestFile fname
  match Run.runLitmusTest model test with
  | .ok () => pure ()
  | .error msg => throw (IO.userError s!"TEST FAILED [{fname.toString}]: {msg}")

#eval runTestFromFile "litmus_tests/MP.archsem.toml" naiveModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" naiveModel
#eval runTestFromFile "litmus_tests/MP+dmbs-unobservable.archsem.toml" naiveModel

#eval runTestFromFile "litmus_tests/MP.archsem.toml" promiseFirstModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" promiseFirstModel
#eval runTestFromFile "litmus_tests/MP+dmbs-unobservable.archsem.toml" promiseFirstModel

end ArchSemTinyArm.Test

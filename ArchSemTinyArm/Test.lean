import ArchSem.LitmusTest.Parse
import ArchSem.LitmusTest.Run
import ArchSemTinyArm.Promising
import ArchSem.TerminatingModel

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open ArchSemTinyArm

namespace ArchSemTinyArm.Test

def fuel : Nat := 10
def naiveModel : ComputationalTerminatingModel Unit :=
  Promising.createNaiveModel sailTinyArmIsem fuel
def promiseFirstModel : ComputationalTerminatingModel Unit :=
  Promising.createPromiseFirstModel sailTinyArmIsem fuel

def runTestFromFile [DecidableEq Flag] [Repr Flag] (fname : System.FilePath)
    (model : ComputationalTerminatingModel Flag) : IO Unit := do
  let test : TestRepr ← Parse.readTestFile fname
  match Run.runLitmusTest test model with
  | .ok () => pure ()
  | .error msg => throw (IO.userError s!"TEST FAILED [{fname.toString}]: {msg}")

#eval runTestFromFile "litmus_tests/MP.archsem.toml" naiveModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" naiveModel
#eval runTestFromFile "litmus_tests/MP+dmbs-unobservable.archsem.toml" naiveModel

#eval runTestFromFile "litmus_tests/MP.archsem.toml" promiseFirstModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" promiseFirstModel
#eval runTestFromFile "litmus_tests/MP+dmbs-unobservable.archsem.toml" promiseFirstModel

end ArchSemTinyArm.Test

import ArchSem.LitmusTest.Basic
import ArchSemTinyArm.Promising

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open ArchSemTinyArm

namespace ArchSemTinyArm.Promising.Test

def fuel : Nat := 10
def naiveModel : ComputationalTerminatingModel :=
  Promising.createNaiveModel sailTinyArmIsem fuel
def promiseFirstModel : ComputationalTerminatingModel :=
  Promising.createPromiseFirstModel sailTinyArmIsem fuel

#eval runTestFromFile "litmus_tests/MP.archsem.toml" naiveModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" naiveModel

#eval runTestFromFile "litmus_tests/MP.archsem.toml" promiseFirstModel
#eval runTestFromFile "litmus_tests/MP+dmbs.archsem.toml" promiseFirstModel

end ArchSemTinyArm.Promising.Test

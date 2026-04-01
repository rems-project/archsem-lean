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

#eval guardTestFromFile true naiveModel "litmus_tests/MP.archsem.toml"
#eval guardTestFromFile true naiveModel "litmus_tests/MP+dmbs.archsem.toml"

#eval guardTestFromFile true promiseFirstModel "litmus_tests/MP.archsem.toml"
#eval guardTestFromFile true promiseFirstModel "litmus_tests/MP+dmbs.archsem.toml"

end ArchSemTinyArm.Promising.Test

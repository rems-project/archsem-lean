import ArchSem.LitmusTest.Basic
import ArchSemTinyArm.Promising

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open ArchSemTinyArm

/-!
This file contains regression tests for all TinyArm concurrency models.
-/

-- TODO: add some more tests here for regression. (maybe diy 6-cycle 2-thread tests?)

namespace ArchSemTinyArm.Promising.Test

def fuel : Nat := 10
def isem : SailM Unit := sailTinyArmIsem

def naiveModel : ComputationalTerminatingModel :=
  Promising.createNaiveModel isem fuel
def promiseFirstModel : ComputationalTerminatingModel :=
  Promising.createPromiseFirstModel isem fuel

#eval guardTestFromFile true naiveModel "litmus_tests/MP.archsem.toml"
#eval guardTestFromFile true naiveModel "litmus_tests/MP+dmbs.archsem.toml"

#eval guardTestFromFile true promiseFirstModel "litmus_tests/MP.archsem.toml"
#eval guardTestFromFile true promiseFirstModel "litmus_tests/MP+dmbs.archsem.toml"

end ArchSemTinyArm.Promising.Test

import ArchSem.LitmusTest.Basic
import ArchSemTinyArm.Promising

open ArchSem.TerminatingModel
open ArchSem.LitmusTest
open ArchSemTinyArm

/-!
This file contains regression tests for all TinyArm concurrency models.
-/

namespace ArchSemTinyArm.Promising.Test

def fuel : Nat := 100
def isem : SailM Unit := sailTinyArmIsem

def naiveModel : ComputationalTerminatingModel :=
  Promising.createNaiveModel isem fuel
def promiseFirstModel : ComputationalTerminatingModel :=
  Promising.createPromiseFirstModel isem fuel

def regressionLitmusTests : List (Bool × String) := [
  (false, "./litmus_tests/arm-small/SB+dmb.sys.archsem.toml"),
  (false, "./litmus_tests/arm-small/R+dmb.sys.archsem.toml"),
  (true, "./litmus_tests/arm-small/2+2W.archsem.toml"),
  (true, "./litmus_tests/arm-small/SB+dmb.sy+po.archsem.toml"),
  (true, "./litmus_tests/arm-small/S.archsem.toml"),
  (false, "./litmus_tests/arm-small/MP+dmb.sys.archsem.toml"),
  (false, "./litmus_tests/arm-small/2+2W+dmb.sys.archsem.toml"),
  (true, "./litmus_tests/arm-small/R+po+dmb.sy.archsem.toml"),
  (true, "./litmus_tests/arm-small/MP.archsem.toml"),
  (true, "./litmus_tests/arm-small/S+po+dmb.sy.archsem.toml"),
  (true, "./litmus_tests/arm-small/LB+dmb.sy+po.archsem.toml"),
  (true, "./litmus_tests/arm-small/MP+po+dmb.sy.archsem.toml"),
  (true, "./litmus_tests/arm-small/SB.archsem.toml"),
  (true, "./litmus_tests/arm-small/R+dmb.sy+po.archsem.toml"),
  (true, "./litmus_tests/arm-small/LB.archsem.toml"),
  (true, "./litmus_tests/arm-small/MP+dmb.sy+po.archsem.toml"),
  (true, "./litmus_tests/arm-small/R.archsem.toml"),
  (true, "./litmus_tests/arm-small/S+dmb.sy+po.archsem.toml"),
  (false, "./litmus_tests/arm-small/S+dmb.sys.archsem.toml"),
  (true, "./litmus_tests/arm-small/2+2W+dmb.sy+po.archsem.toml"),
  (false, "./litmus_tests/arm-small/LB+dmb.sys.archsem.toml"),
]

#eval regressionLitmusTests.forM (fun (allowed,fname)=> guardTestFromFile allowed promiseFirstModel fname)

end ArchSemTinyArm.Promising.Test

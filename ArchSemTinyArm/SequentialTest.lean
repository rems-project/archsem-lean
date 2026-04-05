import ArchSemTinyArm.Sequential
import ArchSemTinyArm.Defs

open Sail.ArchSem
open ArchSemTinyArm.Sequential
open ArchSem.TerminatingModel
open ArchSemTinyArm

/-!
For more comprehensive testing, use the binary test runner.
This file is for debugging purposes: if there is a problem with the model its
nice to have some tests in-code so you can poke around more easily.
For this reason, I allow some repetition between this and other
`{Promising,Sequential}Test.lean`.
-/

namespace ArchSemTinyArm.SequentialTest

def isem : SailM Unit := Out.Functions.fetch_and_execute ()

def extractRegs (regs : List (Fin n × Register)) (archState : ArchState n)
    : List (Option String) :=
  let getRegValue (tid : Fin n) (reg : Register)
      : Option (Arch.register_type reg) :=
    archState.regs[tid].get? reg
  regs.map (fun (tid,reg) => getRegValue tid reg |> Option.map reprStr)

def prepareTestResults [BEq α] (extractor : ArchState n → α)
    (res : List (ModelResult n Unit termCond))
    : List String × List α :=
  res.foldl (fun (errs,results) r => match r with
    | .finalState s _ => (errs, extractor s :: results)
    | .flagged () => (errs.insert "Flagged", results)
    | .error msg => (errs.insert msg, results)
    ) ([], [])

/- Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 -/
namespace EOR

def initialState : ArchState 1 := {
  regs := ⟨#[
      RegisterMap.empty
      |>.insert ._PC (BitVec.ofNat 64 0x500)
      |>.insert .R0 (BitVec.ofNat 64 0x0)
      |>.insert .R1 (BitVec.ofNat 64 0x11)
      |>.insert .R2 (BitVec.ofNat 64 0x101)
    ], rfl⟩
  memory :=
    MemoryMap.empty
    |>.write 4 0x500 0xca020020 /- EOR X0, X1, X2 -/
  addressSpace := default
}

def terminationCondition : TerminationCondition 1 := fun 1 (regs : RegisterMap) =>
  let pc : Option (BitVec 64) := regs.get? ._PC
  pc == some 0x504

def finalStateExtractor : ArchState 1 → List (Option String)
  := extractRegs [(0, .R0)]
def expectedResults := [[some "0x0000000000000110#64"]]

def fuel := 10
def sequentialModel : ComputationalTerminatingModel := createSequentialModel isem fuel

def output := sequentialModel 1 terminationCondition initialState
def results := prepareTestResults finalStateExtractor output

-- Check no errors.
#guard results.fst == []
-- Check expected results.
#guard results.snd.isPerm expectedResults

end EOR

end ArchSemTinyArm.SequentialTest


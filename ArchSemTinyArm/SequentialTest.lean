import ArchSemTinyArm.Sequential
import ArchSemTinyArm.Defs
import Mathlib.Data.Finset.Image

open Sail.ArchSem
open ArchSemTinyArm.Sequential
open ArchSem.TerminatingModel
open ArchSemTinyArm

def isem : SailM Unit := Out.Functions.fetch_and_execute ()

def extractRegs (regs : List (Fin n × Register)) (archState : ArchState n)
    : List (Option String) :=
  let getRegValue (tid : Fin n) (reg : Register)
      : Option (Arch.register_type reg) :=
    archState.regs[tid].get? reg
  regs.map (fun (tid,reg) => getRegValue tid reg |> Option.map reprStr)

def prepareTestResults [DecidableEq α] (extractor : ArchState n → α)
    (res : Finset (ModelResult n Unit termCond))
    : Finset (Except String α) :=
  res.image (fun
    | .finalState s _ => .ok (extractor s)
    | .flagged () => .error "Flagged state"
    | .error msg => .error msg)

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
def expectedResults : Finset (Except String (List (Option String))) :=
  {.ok [some "0x0000000000000110#64"]}

def fuel := 10
def sequentialModel : ComputationalTerminatingModel := createSequentialModel isem fuel

def output := sequentialModel 1 terminationCondition initialState
def results := prepareTestResults finalStateExtractor output
#guard results == expectedResults

end EOR

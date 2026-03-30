import ArchSemTinyArm.Promising
import ArchSemTinyArm.Defs
import Mathlib.Data.Finset.Image

open Sail.ArchSem
open ArchSem.TerminatingModel
open ArchSemTinyArm.Promising
open ArchSemTinyArm

def isem : SailM Unit := sailTinyArmIsem

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

namespace EOR

def initialRegs : RegisterMap :=
  RegisterMap.empty
  |>.insert ._PC (BitVec.ofNat 64 0x500)
  |>.insert .R0 (BitVec.ofNat 64 0x0)
  |>.insert .R1 (BitVec.ofNat 64 0x11)
  |>.insert .R2 (BitVec.ofNat 64 0x101)

def initialMem : MemoryMap :=
  MemoryMap.empty
  |>.write 4 0x500 0xca020020

abbrev nThreads := 1
def initialState : ArchState nThreads := {
  regs := ⟨#[
    initialRegs
  ], rfl⟩,
  memory := initialMem,
  addressSpace := ()
}

def terminationCondition : TerminationCondition nThreads := fun _tid regs =>
  regs.get? ._PC == .some (BitVec.ofNat 64 0x504)

def fuel := 1
def finalStateExtractor : ArchState nThreads → List (Option String)
  := extractRegs [(0, .R0)]
def expectedResults : Finset (Except String (List (Option String))) :=
  {.ok [some "0x0000000000000110#64"]}

def naiveModel : ComputationalTerminatingModel := createNaiveModel isem fuel
def promiseFirstModel : ComputationalTerminatingModel := createPromiseFirstModel isem fuel

def naiveOutput := naiveModel nThreads terminationCondition initialState
def naiveResults := prepareTestResults finalStateExtractor naiveOutput
def promiseFirstOutput := promiseFirstModel nThreads terminationCondition initialState
def promiseFirstResults := prepareTestResults finalStateExtractor promiseFirstOutput

#guard naiveResults == promiseFirstResults
#guard naiveResults == expectedResults

end EOR


namespace MP
/-
A classic MP litmus test
Thread 0: STR X2, [X1, X0]; STR X5, [X4, X3]
Thread 1: LDR X5, [X4, X3]; LDR X2, [X1, X0]

Expected outcome of (R5, R2) at Thread 2:
  (0x1, 0x2a), (0x0, 0x2a), (0x0, 0x0), (0x1, 0x0)
-/

def initialRegsT0 : RegisterMap :=
  RegisterMap.empty
  |>.insert ._PC (BitVec.ofNat 64 0x500)
  |>.insert .R0 (BitVec.ofNat 64 0x1000)
  |>.insert .R1 (BitVec.ofNat 64 0x100)
  |>.insert .R2 (BitVec.ofNat 64 0x2a)
  |>.insert .R3 (BitVec.ofNat 64 0x1000)
  |>.insert .R4 (BitVec.ofNat 64 0x200)
  |>.insert .R5 (BitVec.ofNat 64 0x1)

def initialRegsT1 : RegisterMap :=
  RegisterMap.empty
  |>.insert ._PC (BitVec.ofNat 64 0x600)
  |>.insert .R0 (BitVec.ofNat 64 0x1000)
  |>.insert .R1 (BitVec.ofNat 64 0x100)
  |>.insert .R2 (BitVec.ofNat 64 0x0)
  |>.insert .R3 (BitVec.ofNat 64 0x1000)
  |>.insert .R4 (BitVec.ofNat 64 0x200)
  |>.insert .R5 (BitVec.ofNat 64 0x0)

def initialMem : MemoryMap :=
  MemoryMap.empty
  /- Thread 0 @ 0x500 -/
  |>.write 4 0x500 0xf8206822  /- STR X2, [X1, X0] -/
  |>.write 4 0x504 0xf8236885  /- STR X5, [X4, X3] -/
  /- Thread 1 @ 0x600 -/
  |>.write 4 0x600 0xf8636885  /- LDR X5, [X4, X3] -/
  |>.write 4 0x604 0xf8606822  /- LDR X2, [X1, X0] -/
  /- Backing memory so the addresses exist -/
  |>.write 8 0x1100 0x0
  |>.write 8 0x1200 0x0

abbrev nThreads := 2
def initialState : ArchState nThreads := {
  regs := ⟨#[
    initialRegsT0,
    initialRegsT1
  ], rfl⟩,
  memory := initialMem,
  addressSpace := ()
}

def terminationCondition : TerminationCondition nThreads := fun tid regs =>
  match tid with
  | 0 => regs.get? ._PC == .some (BitVec.ofNat 64 0x508)
  | 1 => regs.get? ._PC == .some (BitVec.ofNat 64 0x608)

def fuel := 6
def finalStateExtractor : ArchState nThreads → List (Option String)
  := extractRegs [(1, .R5), (1, .R2)]
def expectedResults : Finset (Except String (List (Option String))) :=
  { .ok [some "0x0000000000000001#64", some "0x000000000000002a#64"]
  , .ok [some "0x0000000000000001#64", some "0x0000000000000000#64"]
  , .ok [some "0x0000000000000000#64", some "0x000000000000002a#64"]
  , .ok [some "0x0000000000000000#64", some "0x0000000000000000#64"] }

def naiveModel : ComputationalTerminatingModel := createNaiveModel isem fuel
def promiseFirstModel : ComputationalTerminatingModel := createPromiseFirstModel isem fuel

def naiveOutput := naiveModel nThreads terminationCondition initialState
def naiveResults := prepareTestResults finalStateExtractor naiveOutput
def promiseFirstOutput := promiseFirstModel nThreads terminationCondition initialState
def promiseFirstResults := prepareTestResults finalStateExtractor promiseFirstOutput

#guard naiveResults == promiseFirstResults
#guard naiveResults == expectedResults

end MP

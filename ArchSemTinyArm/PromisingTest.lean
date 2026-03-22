import Std.Data.HashSet
import ArchSemTinyArm.Promising
import ArchSemTinyArm.Basic

open Sail.ArchSem
open ArchSem.Promising

/- CR clang: there is some duplication here with sequential tests. -/

def isem : SailM Unit := Out.Functions.fetch_and_execute ()

def memInsert4 (addr : BitVec 64) (value : BitVec 32) (mem : InitialMem) :=
  assert! (addr.getLsb 0) == false
  assert! (addr.getLsb 1) == false
  if addr.getLsb 2 then /- Upper half. -/
    let word : BitVec 64 := mem.getD (addr >>> 3) (BitVec.zero 64)
    let word := word &&& (BitVec.ofInt 64 (0xFFFFFFFF))
    let word := word ||| (value.zeroExtend 64 <<< 32)
    mem.insert (addr >>> 3) word
  else /- Lower half. -/
    let word := mem.getD (addr >>> 3) (BitVec.zero 64)
    let word := word &&& (BitVec.ofInt 64 (0xFFFFFFFF <<< 32))
    let word := word ||| value
    mem.insert (addr >>> 3) word

def extractRegs (regs : List (Fin n × Register)) (mstate : ModelState n)
    : List (Option String) :=
  let getRegValue (tid : Fin n) (reg : Register)
      : Option (Arch.register_type reg) :=
    mstate.threadStates[tid].regs.get? reg |> Option.map Prod.fst
  regs.map (fun (tid,reg) => getRegValue tid reg |> Option.map reprStr)

def prepareTestResults [BEq α] [Hashable α] (extractor : ModelState n → α)
    (res : ExecutionMonad.NResult (ModelState n × String) (ModelState n × ModelState n) )
    : List String × Std.HashSet α :=
  let errs := res.errors.map (fun (_mstate,err) => err)
  let finalStates := res.results.map Prod.snd
  let results := finalStates.map extractor
  (errs, Std.HashSet.ofList results)

namespace EOR

def initialRegs : RegisterMap :=
  RegisterMap.empty
  |>.insert ._PC (BitVec.ofNat 64 0x500)
  |>.insert .R0 (BitVec.ofNat 64 0x0)
  |>.insert .R1 (BitVec.ofNat 64 0x11)
  |>.insert .R2 (BitVec.ofNat 64 0x101)

def initialMem : InitialMem :=
  (Std.ExtHashMap.emptyWithCapacity 32)
  |> memInsert4 0x500 0xca020020

abbrev nThreads := 1
def initialState : ModelState nThreads := {
  threadStates := ⟨#[
    ThreadState.init initialRegs
  ], rfl⟩,
  initmem := initialMem,
  mem := []
}

def terminationCondition : TerminationCondition nThreads := fun _tid regs =>
  regs.get? ._PC == .some (BitVec.ofNat 64 0x504)

def fuel := 1
def finalStateExtractor : ModelState nThreads → List (Option String)
  := extractRegs [(0, .R0)]
def expectedFinalStates := Std.HashSet.ofList [[some "0x0000000000000110#64"]]

def results := run fuel isem terminationCondition initialState
def output := prepareTestResults finalStateExtractor results

def promiseFirstResults := runPromiseFirst fuel isem terminationCondition initialState
def promiseFirstOutput := prepareTestResults finalStateExtractor results

#guard output == promiseFirstOutput
#guard output == ([], expectedFinalStates)

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

def initialMem : InitialMem :=
  (Std.ExtHashMap.emptyWithCapacity 32)
  /- Thread 0 @ 0x500 -/
  |> memInsert4 0x500 0xf8206822  /- STR X2, [X1, X0] -/
  |> memInsert4 0x504 0xf8236885  /- STR X5, [X4, X3] -/
  /- Thread 1 @ 0x600 -/
  |> memInsert4 0x600 0xf8636885  /- LDR X5, [X4, X3] -/
  |> memInsert4 0x604 0xf8606822  /- LDR X2, [X1, X0] -/
  /- Backing memory so the addresses exist -/
  |>.insert (0x1100 >>> 3) 0x0
  |>.insert (0x1200 >>> 3) 0x0

abbrev nThreads := 2
def initialState : ModelState nThreads := {
  threadStates := ⟨#[
    ThreadState.init initialRegsT0,
    ThreadState.init initialRegsT1
  ], rfl⟩,
  initmem := initialMem,
  mem := []
}

def terminationCondition : TerminationCondition nThreads := fun tid regs =>
  match tid with
  | 0 => regs.get? ._PC == .some (BitVec.ofNat 64 0x508)
  | 1 => regs.get? ._PC == .some (BitVec.ofNat 64 0x608)

def fuel := 6
def finalStateExtractor : ModelState nThreads → List (Option String)
  := extractRegs [(1, .R5), (1, .R2)]
def expectedFinalStates := Std.HashSet.ofList [
  [some "0x0000000000000001#64", some "0x000000000000002a#64"],
  [some "0x0000000000000001#64", some "0x0000000000000000#64"],
  [some "0x0000000000000000#64", some "0x000000000000002a#64"],
  [some "0x0000000000000000#64", some "0x0000000000000000#64"]]

def results := run fuel isem terminationCondition initialState
def output := prepareTestResults finalStateExtractor results

def promiseFirstResults := runPromiseFirst fuel isem terminationCondition initialState
def promiseFirstOutput := prepareTestResults finalStateExtractor results

#guard output == promiseFirstOutput
#guard output == ([], expectedFinalStates)

end MP

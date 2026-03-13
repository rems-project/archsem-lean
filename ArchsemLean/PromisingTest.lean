import Out.Defs
import Out.TinyArm
import ArchsemLean.Promising

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

-- CR clang: get rid of this..
--def getPC (ts : ThreadState) : BitVec 64 :=
--  ts.regs.getD ._PC default |> Prod.fst

def extractRegs (regs : List (Fin n × Register)) (mstate : ModelState n) : List String :=
  let getRegValueD (tid : Fin n) (reg : Register) : Arch.register_type reg :=
    mstate.threadStates[tid].regs.getD reg (default, 0) |> Prod.fst
  regs.map (fun (tid,reg) => getRegValueD tid reg |> reprStr)

def prepareTestResults [BEq α] (extractor : ModelState n → α)
    (res : ExecutionMonad.NResult (ModelState n × String) (ModelState n × ModelState n) )
    : List (Except String α) :=
  let errToString (mstate : ModelState n) (err : String) :=
    -- CR clang: remove this compments
    --let pcs := mstate.threadStates.toList.mapIdx
    --  (fun tid tstate =>
    --    s!"T{tid}@0x{(getPC tstate).toHex}")
    err -- ++ " " ++ (" ".intercalate pcs)
  let errs := res.errors.map (fun (mstate,err) => Except.error (errToString mstate err))
  let finalStates := res.results.map Prod.snd
  let results := finalStates.map (Except.ok ∘ extractor)
  results.eraseDups ++ errs

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

def testResults := runPromiseFirst fuel isem terminationCondition initialState

#guard prepareTestResults (extractRegs [(0, .R0)]) testResults ==
  [Except.ok ["0x0000000000000110#64"]]

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

def testResults := run fuel isem terminationCondition initialState
def promisingFirstTestResults := runPromiseFirst fuel isem terminationCondition initialState

def testOutput := prepareTestResults (extractRegs [(1, .R5), (1, .R2)]) testResults
def promisingFirstTestOutput := prepareTestResults (extractRegs [(1, .R5), (1, .R2)]) promisingFirstTestResults

-- CR clang: TODO use a set instead of list to allow for reordering...
#guard testOutput == promisingFirstTestOutput
#guard testOutput == [
  Except.ok ["0x0000000000000001#64", "0x000000000000002a#64"],
  Except.ok ["0x0000000000000001#64", "0x0000000000000000#64"],
  Except.ok ["0x0000000000000000#64", "0x000000000000002a#64"],
  Except.ok ["0x0000000000000000#64", "0x0000000000000000#64"]]

end MP

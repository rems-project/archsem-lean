import Out.Defs
import Out.TinyArm
import ArchsemLean.Promising

open Sail.ArchSem
open ArchSem.Promising

/- CR clang: there is some duplication here with sequentialtests. -/

def isem : SailM Unit := Out.Functions.fetch_and_execute ()

def memInsert4 (addr : BitVec 64) (value : BitVec 32) (mem : InitialMem) :=
  assert! (addr.getLsb 0) == false
  assert! (addr.getLsb 1) == false
  if addr.getLsb 2 then /- Upper half. -/
    let word : BitVec 64 := mem.getD (addr >>> 3) (BitVec.zero 64)
    let word := word &&& (BitVec.ofInt 64 (0xFFFFFFFF <<< 32))
    let word := word ||| (value <<< 32)
    mem.insert (addr >>> 3) word
  else /- Lower half. -/
    let word := mem.getD (addr >>> 3) (BitVec.zero 64)
    let word := word &&& (BitVec.ofInt 64 0xFFFFFFFF)
    let word := word ||| value
    mem.insert (addr >>> 3) word

def extractRegs (regs : List Register) (ts : ThreadState) : String :=
  let getRegValue (reg : Register) : Arch.register_type reg :=
    ts.regs.getD reg (default, 0) |> Prod.fst
  let strings := regs.map (fun reg =>
    let value := getRegValue reg
    (reprStr reg) ++ "=" ++ (reprStr value))
  " ".intercalate strings

def prepareTestResults (extractor : ThreadState → String)
    (res : ExecutionMonad.NResult (ModelState n × String) (ModelState n × ModelState n) )
    : List (Except String (List String)) :=
  let errs := res.errors.map (Except.error ∘ Prod.snd)
  let finalStates := res.results.map (Vector.toList ∘ ModelState.threadStates ∘ Prod.snd)
  let finalStatesString := finalStates.map (fun threads => threads.map extractor)
  let results := finalStatesString.map Except.ok
  results ++ errs

section EOR

def initialRegs : RegisterMap :=
  RegisterMap.empty
  |>.insert ._PC (BitVec.ofNat 64 0x500)
  |>.insert .R0 (BitVec.ofNat 64 0x0)
  |>.insert .R1 (BitVec.ofNat 64 0x11)
  |>.insert .R2 (BitVec.ofNat 64 0x101)

def initialMem : InitialMem :=
  (Std.ExtHashMap.emptyWithCapacity 32)
  |> memInsert4 0x500 0xca020020

def initialState : ModelState 1 := {
  threadStates := ⟨#[
    ThreadState.init initialRegs
  ], rfl⟩,
  initmem := initialMem,
  mem := [],
}

def terminationCondition : TerminationCondition 1 := fun _tid regs =>
  regs.get? ._PC == .some (BitVec.ofNat 64 0x504)

def fuel := 1

def testResults := runPromiseFirst fuel isem terminationCondition initialState

#guard prepareTestResults (extractRegs [.R0]) testResults ==
  [Except.ok ["Register.R0=0x0000000000000110#64"]]

end EOR

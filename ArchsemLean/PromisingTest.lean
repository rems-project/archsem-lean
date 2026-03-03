import Out.Defs
import Out.TinyArm
import ArchsemLean.Promising

open Sail.ArchSem

/- CR clang: there is some duplication here with sequentialtests. -/

instance : DecidableEq Arch.register := by
  have eq : Arch.register = Register := rfl
  rw [eq]
  infer_instance
instance : Hashable Arch.register := by
  have eq : Arch.register = Register := rfl
  rw [eq]
  infer_instance

instance : BEq (Arch.register_type ._PC) := by
  have eq : Arch.register_type = RegisterType := rfl
  rw [eq]
  infer_instance

section EOR

def initialRegs : Std.ExtDHashMap Arch.register Arch.register_type :=
  (Std.ExtDHashMap.emptyWithCapacity 64)
  |>.insert ._PC (BitVec.ofNat 64 0x500)
  |>.insert .R0 (BitVec.ofNat 64 0x0)
  |>.insert .R1 (BitVec.ofNat 64 0x11)
  |>.insert .R2 (BitVec.ofNat 64 0x101)

def initialMem : InitialMem :=
  (Std.ExtHashMap.emptyWithCapacity 32)
  /- CR clang: write a mem_insert helper. -/
  |>.insert (0x500 >>> 3) 0xca020020

def initialState : ModelState 1 := {
  threadStates := ⟨#[
    ThreadState.init initialRegs
  ], rfl⟩,
  initmem := initialMem,
  mem := [],
}

def termination (_tid : Nat) (regs : Std.ExtDHashMap Arch.register  Arch.register_type) : Bool :=
  regs.get? ._PC == .some (BitVec.ofNat 64 0x504)

def isem : SailM Unit := Out.Functions.fetch_and_execute ()
def fuel := 1

def outputTState (tstate : ThreadState) : String :=
  let r0 : Option (BitVec 64) := (tstate.regs.get? .R0).map (Prod.fst)
  toString r0


def testOutput : String :=
  let res := runPromiseFirst fuel isem termination initialState
  match res.errors with
  | [] => "output:\n" ++ "\n".intercalate
    ((res.results.map Prod.snd).map (fun pstate => outputTState pstate.threadStates[0]))
  | errs => "errors:\n" ++ "\n".intercalate (errs.map Prod.snd)

#eval testOutput

end EOR

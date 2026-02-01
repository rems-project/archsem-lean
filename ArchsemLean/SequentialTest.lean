import Out.Defs
import Out.Sail.Sequential
import Out.TinyArm

#check ArchSem.Arch
#check SequentialState
#check ChoiceSource

open ArchSem

example : Arch.register = Register := by
  rfl

/- CR chris: I dont understand why lean4 cant figure this out in its own. -/
instance : DecidableEq Arch.register := by
  have eq : Arch.register = Register := rfl
  rw [eq]
  infer_instance
instance : Hashable Arch.register := by
  have eq : Arch.register = Register := rfl
  rw [eq]
  infer_instance

def memInsert (addr : Nat) (size : Nat) (value : Nat) (mem : (Std.ExtHashMap Nat (BitVec 8))) :=
  let list := List.ofFn (fun i : Fin size => (addr + i.val, BitVec.ofNat 8 (value >>> (i.val * 8))))
  list.foldl (fun acc (addr, byte) => acc.insert addr byte) mem

def choiceSource := trivialChoiceSource
/-
    Std.ExtDHashMap.insert default Register._PC (BitVec.ofNat 64 100)
    
      |> mem_insert 0x500 4 0xca020020. (* EOR X0, X1, X2 *)

-/

def initialState : SequentialState choiceSource := {
  regs :=
    (Std.ExtDHashMap.emptyWithCapacity 64)
    |>.insert ._PC (BitVec.ofNat 64 0x500)
    |>.insert .R0 (BitVec.ofNat 64 0x0)
    |>.insert .R1 (BitVec.ofNat 64 0x11)
    |>.insert .R2 (BitVec.ofNat 64 0x101)
  choiceState := ()
  mem :=
    (Std.ExtHashMap.emptyWithCapacity 32)
    |> memInsert 0x500 4 0xca020020 /- EOR X0, X1, X2 -/
  tags := ()
  cycleCount := 0
  sailOutput := Array.empty
}

def main : IO UInt32 :=
  let freeMonad := Out.Functions.fetch_and_execute ()
  let stateMonad := sequentialInterpreter freeMonad
  let result := stateMonad.run initialState
  match result with
  | .ok _ s => do
    let out : Option (BitVec 64) := s.regs.get? .R0
    IO.print s!"output: {out}"
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

#eval main

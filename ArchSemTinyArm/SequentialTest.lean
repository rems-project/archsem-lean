import ArchSemTinyArm.Sequential
import ArchSemTinyArm.Basic

open Sail.ArchSem
open ArchSemTinyArm.Sequential
open ArchSem.TerminatingModel
open ArchSemTinyArm

/- CR clang for leo: I dont understand why lean4 cant figure this out in its own. -/
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

def outputSequentialState (info : SequentialState choiceSource → String)
    : EStateM.Result (Sail.Error exception) (SequentialState choiceSource) Unit → String
  | .ok _ s =>
    /- let out : Option (BitVec _) := s.regs.get? reg -/
    s!"output: {info s}\n" ++ "\n".intercalate s.sailOutput.toList
  | .error e s =>
    s!"error: {e.print}\n" ++ "\n".intercalate s.sailOutput.toList

/- Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 -/
namespace EOR

def choiceSource := trivialChoiceSource
def initialState : SequentialState choiceSource := {
  regs :=
    (Std.DHashMap.emptyWithCapacity 64)
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

def terminationCondition : TerminationCondition 1 := fun 1 (regs : RegisterMap) =>
  let pc : Option (BitVec 64) := regs.get? ._PC
  pc == some 0x504

def eor_output : String :=
  let isem := sailTinyArmIsem
  let fuel := 20
  let model := sequentialModel fuel isem terminationCondition
  -- let stateMonad := sequentialInterpreter freeMonad
  let result := model.run initialState
  /- CR clang: why cant this be (fun s => toString (s.regs.get? .R0)) -/
  outputSequentialState (fun s =>
    let out : Option (BitVec 64) := (s.regs.get? .R0)
    toString out
  ) result

#guard eor_output == "output: (some 0x0000000000000110#64)\n"

end EOR

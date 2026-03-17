import Std.Data.ExtDHashMap
import Out.Defs
import Sail

open Sail.ArchSem

/-
 - CR clang for leo: we should modify the Arch interface and sail-lean backend to
 - have this typeclass instance in Arch.
 - It would be nice to have toString instances for registers and register types.
 -/
/-
instance (reg : Register) : BEq (Arch.register_type reg) := by
  have eq : Arch.register_type = RegisterType := rfl
  rw [eq]
  rw [RegisterType.eq_def]
  split <;> infer_instance
instance (reg : Register) : Inhabited (Arch.register_type reg) := by
  have eq : Arch.register_type = RegisterType := rfl
  rw [eq]
  rw [RegisterType.eq_def]
  split <;> infer_instance
instance (reg : Register) : Repr (Arch.register_type reg) := by
  have eq : Arch.register_type = RegisterType := rfl
  rw [eq]
  rw [RegisterType.eq_def]
  split <;> infer_instance
-/


/-
CR clang for leo: I'm amazed lean does not have this in core libs?!
I need it for guarding test results.
-/
instance [BEq α] [BEq β] : BEq (Except α β) where
  beq
    | .error e1, .error e2 => e1 == e2
    | .ok v1, .ok v2 => v1 == v2
    | _, _ => false

/-
 - If we are in a context where the number of threads is known then we prefer
 - to use `Fin nThreads`. But to avoid having to pass nThreads around everywhere,
 - sometimes we just want to use a Nat. And its nice to give this Nat a descriptive
 - name like `Tid`.
 -/
abbrev Tid := Nat

abbrev RegisterMap [Arch] := Std.ExtDHashMap Arch.register Arch.register_type
abbrev TerminationCondition [Arch] (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

def RegisterMap.empty : RegisterMap := Std.ExtDHashMap.emptyWithCapacity 64

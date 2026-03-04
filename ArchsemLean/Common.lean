import Std.Data.ExtDHashMap
import Out.Defs
import Sail

open Sail.ArchSem

/-
 - CR clang for leo: we should modify the Arch interface and sail-lean backend to
 - have this typeclass instance in Arch.
 -/
instance : BEq (Arch.register_type ._PC) := by
  have eq : Arch.register_type = RegisterType := rfl
  rw [eq]
  infer_instance

/-
 - If we are in a context where the number of threads is known then we prefer
 - to use `Fin nThreads`. But to avoid having to pass nThreads around everywhere,
 - sometimes we just want to use a Nat. And its nice to give this Nat a descriptive
 - name like `Tid`.
 -/
abbrev Tid := Nat

abbrev RegisterMap [Arch] := Std.ExtDHashMap Arch.register Arch.register_type
abbrev TerminationCondition [Arch] (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

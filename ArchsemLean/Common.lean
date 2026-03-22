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

class ArchExtra [Arch] where
  /- Comparison instances. -/
  register_type_deq (reg : Arch.register) : DecidableEq (Arch.register_type reg)
  /- Repr instances. -/
  addr_space_repr : Repr Arch.addr_space
  register_repr : Repr Arch.register
  register_type_repr (reg : Arch.register) : Repr (Arch.register_type reg)
  mem_acc_repr : Repr Arch.mem_acc
  trans_start_repr : Repr Arch.trans_start
  trans_end_repr : Repr Arch.trans_end
  abort_repr : Repr Arch.abort
  barrier_repr : Repr Arch.barrier
  cache_op_repr : Repr Arch.cache_op
  tlbi_repr : Repr Arch.tlbi
  exn_repr : Repr Arch.exn
  sys_reg_id_repr : Repr Arch.sys_reg_id

instance [ArchExtra] (reg : Arch.register) : DecidableEq (Arch.register_type reg) := ArchExtra.register_type_deq reg
instance [ArchExtra] : Repr Arch.addr_space  := ArchExtra.addr_space_repr
instance [ArchExtra] : Repr Arch.register    := ArchExtra.register_repr
instance [ArchExtra] (reg : Arch.register) : Repr (Arch.register_type reg) := ArchExtra.register_type_repr reg
instance [ArchExtra] : Repr Arch.mem_acc     := ArchExtra.mem_acc_repr
instance [ArchExtra] : Repr Arch.trans_start := ArchExtra.trans_start_repr
instance [ArchExtra] : Repr Arch.trans_end   := ArchExtra.trans_end_repr
instance [ArchExtra] : Repr Arch.abort       := ArchExtra.abort_repr
instance [ArchExtra] : Repr Arch.barrier     := ArchExtra.barrier_repr
instance [ArchExtra] : Repr Arch.cache_op    := ArchExtra.cache_op_repr
instance [ArchExtra] : Repr Arch.tlbi        := ArchExtra.tlbi_repr
instance [ArchExtra] : Repr Arch.exn         := ArchExtra.exn_repr
instance [ArchExtra] : Repr Arch.sys_reg_id  := ArchExtra.sys_reg_id_repr


/-
 - If we are in a context where the number of threads is known then we prefer
 - to use `Fin nThreads`. But to avoid having to pass nThreads around everywhere,
 - sometimes we just want to use a Nat. And its nice to give this Nat a descriptive
 - name like `Tid`.
 -/
abbrev Tid := Nat

abbrev RegisterMap [ArchExtra] := Std.ExtDHashMap Arch.register Arch.register_type
abbrev TerminationCondition [ArchExtra] (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

def RegisterMap.empty [ArchExtra] : RegisterMap := Std.ExtDHashMap.emptyWithCapacity 64

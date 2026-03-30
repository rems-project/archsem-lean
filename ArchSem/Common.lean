import Std.Data.ExtDHashMap
import Out.Defs
import Sail

open Sail.ArchSem

/--
Register value generator.
An architecture can define its registers to be of any type
but to have a portable test format we want a general way of defining
register values.
A RegValGen type can be parsed from a toml file and converted into
an architecture register type using a function from ArchExtra.
-/
inductive RegValGen where
  | number (n : Int)
  | string (s : String)
  | array (l : List RegValGen)
  | struct (l : List (String × RegValGen))
deriving Repr

/--
ArchExtra is an extension of the Arch typeclass implemented by the lean-sail backend.
We implement the extra fields and functions for each Architecture we wish to use in ArchSem.
This allows us to add new features without changing the sail backend.
-/
class ArchExtra [Arch] where
  /-
  Registers must have a total (linear) order. This is necessary for efficiently defining
  equality on an register to value map implementation.
  -/
  register_ord : Ord Arch.register
  register_trans : Std.TransCmp register_ord.compare
  register_lawful_eq_cmp : Std.LawfulEqCmp register_ord.compare
  -- register_lawful_eq_cmp : Std.LawfulEqCmp register_ord register_ord.compare
  /- There must be a default address space to be used in litmus tests. -/
  addr_space_inhabited : Inhabited Arch.addr_space
  /- Comparisons are required for checking final states in litmus tests. -/
  register_type_deq (reg : Arch.register) : DecidableEq (Arch.register_type reg)
  addr_space_deq : DecidableEq Arch.addr_space
  /- Registers are named by string in the litmus test format. -/
  register_of_string : String → Except String Arch.register
  register_type_of_gen (reg : Arch.register) : RegValGen → Except String (Arch.register_type reg)
  /- Architecture types get Repr instances to make debugging easier. -/
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

/- Help lean4's type inference find the instances in ArchExtra. -/
instance [ArchExtra] : Ord Arch.register := ArchExtra.register_ord
instance [ArchExtra] : Std.TransCmp ArchExtra.register_ord.compare := ArchExtra.register_trans
instance [ArchExtra] : Std.LawfulEqCmp ArchExtra.register_ord.compare := ArchExtra.register_lawful_eq_cmp
instance [ArchExtra] : Inhabited Arch.addr_space  := ArchExtra.addr_space_inhabited
instance [ArchExtra] (reg : Arch.register) : DecidableEq (Arch.register_type reg) := ArchExtra.register_type_deq reg
instance [ArchExtra] : DecidableEq Arch.addr_space  := ArchExtra.addr_space_deq
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


/--
Thread ID.
If we are in a context where the number of threads is known then we prefer
to use `Fin nThreads`. But to avoid having to pass nThreads around everywhere,
sometimes we just want to use a Nat. And its nice to give this Nat a descriptive
name like `Tid`.
-/
abbrev Tid := Nat

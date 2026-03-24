import Std.Data.ExtHashMap
import Std.Data.HashSet
import ArchSem.Common
import Sail

open Sail.ArchSem

-- CR clang: comment this code similar to archsem comments.

namespace ArchSem.TerminatingModel

variable [ArchExtra]
abbrev Address := BitVec Arch.addr_size
def MemoryMap := Std.HashMap Address (BitVec 8)
deriving BEq
def MemoryMap.empty : MemoryMap := Std.HashMap.emptyWithCapacity 1024
def MemoryMap.readByte (addr : Address) (mem : MemoryMap) : BitVec 8 :=
  mem.getD addr 0
def MemoryMap.read (size : Nat) (addr : Address) (mem : MemoryMap) : BitVec (8 * size) :=
  let bytes : Vector (BitVec 8) size := Vector.ofFn (fun i => mem.readByte (addr + i.val))
  Sail.vecbytes_to_bitvec bytes
def MemoryMap.insertByte (addr : Address) (byte : BitVec 8) (mem : MemoryMap)
    : MemoryMap :=
  mem.insert addr byte
def MemoryMap.insert (size : Nat) (addr : Address) (word : BitVec (8 * size)) (mem : MemoryMap)
    : MemoryMap :=
  let bytes := Sail.bitvec_to_vecbytes word
  (List.finRange size).foldl (fun m i => m.insertByte (addr + i.val) bytes[i]) mem

-- CR clang: MemoryMap manipulation functions
-- CR clang: RegisterMap should probably be just a DHasmMap.
def RegisterMap [ArchExtra] := Std.DHashMap Arch.register Arch.register_type
deriving BEq
def RegisterMap.empty [ArchExtra] : RegisterMap := Std.DHashMap.emptyWithCapacity 64
-- CR clang: RegisterMap manipulation functions
abbrev TerminationCondition [ArchExtra] (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

structure ArchState (nThreads : Nat) where
  memory : MemoryMap
  addressSpace : Arch.addr_space
  regs : Vector RegisterMap nThreads
deriving BEq

def ArchState.has_terminated (termCond : TerminationCondition nThreads)
    (s : ArchState nThreads) : Prop :=
  ∀ tid : Fin nThreads, termCond tid s.regs[tid]

-- def HasTerminated ...
-- (List.finRange nThreads).all (fun tid => termCond tid s.regs[tid])

inductive ModelResult (nThreads : Nat) (Flag : Type) (termCond : TerminationCondition nThreads)
  | finalState (s : ArchState nThreads) (t : s.has_terminated termCond)
  | flagged (f : Flag)
  | error (msg : String)

instance [BEq Flag] : BEq (ModelResult n Flag termCond) where
  beq
    | .finalState s₁ _, .finalState s₂ _ => s₁ == s₂
    | .flagged f₁, .flagged f₂ => f₁ == f₂
    | .error m₁, .error m₂ => m₁ == m₂
    | _, _ => false

def ComputationalTerminatingModel (Flag : Type) [DecidableEq Flag] :=
  {nThreads : Nat} → (termCond : TerminationCondition nThreads) →
  ArchState nThreads → ListSet (ModelResult nThreads Flag termCond)

end ArchSem.TerminatingModel

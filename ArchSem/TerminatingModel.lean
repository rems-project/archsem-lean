import Std.Data.ExtHashMap
import Std.Data.HashSet
import ArchSem.Common
import Sail

open Sail.ArchSem

/-
This file provides a general definition for terminating architecture
concurrency models.
-/

namespace ArchSem.TerminatingModel

variable [ArchExtra]

abbrev Address := BitVec Arch.addr_size

/--
An architecture memory map. We assume bytes of 8-bits indexed by an address bit vector.
-/
def MemoryMap := Std.HashMap Address (BitVec 8) deriving BEq

namespace MemoryMap

def empty : MemoryMap := Std.HashMap.emptyWithCapacity 1024

def readByte (addr : Address) (mem : MemoryMap) : BitVec 8 :=
  mem.getD addr 0

/-- Read a little-endian word of `size` from memory. -/
def read (size : Nat) (addr : Address) (mem : MemoryMap) : BitVec (8 * size) :=
  let bytes : Vector (BitVec 8) size := Vector.ofFn (fun i => mem.readByte (addr + i.val))
  Sail.vecbytes_to_bitvec bytes

def writeByte (addr : Address) (byte : BitVec 8) (mem : MemoryMap)
    : MemoryMap :=
  mem.insert addr byte

/-- Write a little-endian word of `size` from memory. -/
def write (size : Nat) (addr : Address) (word : BitVec (8 * size)) (mem : MemoryMap)
    : MemoryMap :=
  let bytes := Sail.bitvec_to_vecbytes word
  (List.finRange size).foldl (fun m i => m.writeByte (addr + i.val) bytes[i]) mem

end MemoryMap

/-- An architecture register map. -/
def RegisterMap [ArchExtra] := Std.DHashMap Arch.register Arch.register_type
deriving BEq

def RegisterMap.empty [ArchExtra] : RegisterMap := Std.DHashMap.emptyWithCapacity 64

abbrev TerminationCondition [ArchExtra] (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

/-- The generalized inter-instruction architecture state.  -/
structure ArchState (nThreads : Nat) where
  memory : MemoryMap
  addressSpace : Arch.addr_space
  regs : Vector RegisterMap nThreads
deriving BEq

def ArchState.has_terminated (termCond : TerminationCondition nThreads)
    (s : ArchState nThreads) : Prop :=
  ∀ tid : Fin nThreads, termCond tid s.regs[tid]

/--
The result type returned from an architecture concurrency model after a termination condition.
-/
inductive ModelResult (nThreads : Nat) (Flag : Type) (termCond : TerminationCondition nThreads)
  /- A final state comes with a proof its terminated. -/
  | finalState (s : ArchState nThreads) (t : s.has_terminated termCond)
  | flagged (f : Flag)
  | error (msg : String)

instance [BEq Flag] : BEq (ModelResult n Flag termCond) where
  beq
    | .finalState s₁ _, .finalState s₂ _ => s₁ == s₂
    | .flagged f₁, .flagged f₂ => f₁ == f₂
    | .error m₁, .error m₂ => m₁ == m₂
    | _, _ => false

-- CR clang for thibaut: archsem passed Flag to this type. Lets discuss.
def ComputationalTerminatingModel :=
  (nThreads : Nat) → (termCond : TerminationCondition nThreads) →
  ArchState nThreads → ListSet (ModelResult nThreads Unit termCond)

-- TODO: non-computational model definition.

end ArchSem.TerminatingModel

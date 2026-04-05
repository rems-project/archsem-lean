import Std.Data.ExtTreeMap
import Sail
import ArchSem.Defs

open Sail.ArchSem

/-!
This file provides a general definition for terminating architecture
concurrency models.
-/

namespace ArchSem.TerminatingModel

variable [Arch] [ArchExtra]

abbrev Address := BitVec Arch.addr_size

/--
An architecture memory map. We assume bytes of 8-bits indexed by a bit vector.
-/
def MemoryMap := Std.ExtTreeMap Address (BitVec 8)
deriving DecidableEq

namespace MemoryMap

def empty : MemoryMap := Std.ExtTreeMap.empty

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
def RegisterMap [ArchExtra] := Std.ExtDTreeMap Arch.register Arch.register_type
deriving DecidableEq

def RegisterMap.empty : RegisterMap := Std.ExtDTreeMap.empty

/--
When the termination condition returns true on all threads, the model
should stop executing.

The tid and associated register map is passed for each thread.
-/
abbrev TerminationCondition (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

/-- The generalized inter-instruction architecture state.  -/
structure ArchState (nThreads : Nat) where
  memory : MemoryMap
  addressSpace : Arch.addr_space
  regs : Vector RegisterMap nThreads
deriving DecidableEq

/--
A decidable proposition as to weather an architecture state satisfies
ther termination condition.
-/
def ArchState.has_terminated (termCond : TerminationCondition nThreads)
    (s : ArchState nThreads) : Prop :=
  ∀ tid : Fin nThreads, termCond tid s.regs[tid]

-- CR clang: If I implement decidable on `has_terminated` will it automatically
-- get decidable eq? I'm supprised that all propositions are not already
-- DecidableEq. Aren't all propositions of the same type equal?

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

/---
To implement DecidableEq for ModelResult, it is insufficient to add
`deriving DecidableEq` since the inductive type contains `s.has_terminated termCond`
which is a proposition type and does not itself implement DecidableEq.
-/
instance [DecidableEq Flag] (n : Nat) (termCond : TerminationCondition n)
    : DecidableEq (ModelResult n Flag termCond) := by
   intro r₁ r₂
   cases r₁ <;> cases r₂
   case finalState.finalState =>
     rename_i s₁ _ s₂ _
     by_cases s₁ = s₂
     · exact isTrue (by simp; assumption)
     · exact isFalse (by simp; assumption)
   case flagged.flagged =>
     rename_i f₁ f₂
     simpa using (inferInstance : Decidable (f₁ = f₂))
   case error.error =>
     rename_i m₁ m₂
     simpa using (inferInstance : Decidable (m₁ = m₂))
   all_goals exact (isFalse (by intro h; contradiction))   
 
-- CR clang for thibaut: archsem passed Flag to this type. Lets discuss.
def ComputationalTerminatingModel :=
  (nThreads : Nat) → (termCond : TerminationCondition nThreads) →
  ArchState nThreads → List (ModelResult nThreads Unit termCond)

-- TODO: non-computational model definition.

end ArchSem.TerminatingModel

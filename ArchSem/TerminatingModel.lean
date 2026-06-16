-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Std.Data.ExtTreeMap
import Sail
import ArchSem.Defs
import ArchSem.ListSet

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
deriving DecidableEq, Ord

instance : Std.TransCmp (compare : MemoryMap → MemoryMap → Ordering) := by
  change Std.TransCmp (compare : Std.ExtTreeMap Address (BitVec 8) → Std.ExtTreeMap Address (BitVec 8) → Ordering)
  infer_instance

instance : Std.LawfulEqCmp (compare : MemoryMap → MemoryMap → Ordering) := by
  change Std.LawfulEqCmp (compare : Std.ExtTreeMap Address (BitVec 8) → Std.ExtTreeMap Address (BitVec 8) → Ordering)
  infer_instance

instance : Hashable MemoryMap where
  hash mem := mem.foldl (fun acc addr value => acc.xor (hash (addr, value))) 0

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
deriving DecidableEq, Ord

instance : Std.TransCmp (compare : RegisterMap → RegisterMap → Ordering) := by
  change Std.TransCmp (compare : Std.ExtDTreeMap Arch.register Arch.register_type →
    Std.ExtDTreeMap Arch.register Arch.register_type → Ordering)
  infer_instance

instance : Std.LawfulEqCmp (compare : RegisterMap → RegisterMap → Ordering) := by
  change Std.LawfulEqCmp (compare : Std.ExtDTreeMap Arch.register Arch.register_type →
    Std.ExtDTreeMap Arch.register Arch.register_type → Ordering)
  infer_instance

instance : Hashable RegisterMap where
  hash regs := regs.foldl (fun acc addr value => acc.xor (hash (addr, value))) 0

def RegisterMap.empty : RegisterMap := Std.ExtDTreeMap.empty

/--
When the termination condition returns true on all threads, the model
should stop executing.

The tid and associated register map is passed for each thread.
-/
abbrev TerminationCondition (nThreads : Nat) := Fin nThreads → RegisterMap → Bool

instance [Hashable α] : Hashable (Vector α n) where
  hash vec := hash vec.toArray

/-- The generalized inter-instruction architecture state.  -/
structure ArchState (nThreads : Nat) where
  memory : MemoryMap
  addressSpace : Arch.addr_space
  regs : Vector RegisterMap nThreads
deriving DecidableEq, Hashable

instance : Ord (ArchState nThreads) where
  compare := compareOn (fun s => (s.memory, s.addressSpace, s.regs))

instance : Std.TransCmp (compare : ArchState nThreads → ArchState nThreads → Ordering) := by
  change Std.TransCmp (compareOn (fun s : ArchState nThreads => (s.memory, s.addressSpace, s.regs)))
  infer_instance

instance : Std.LawfulEqCmp (compare : ArchState nThreads → ArchState nThreads → Ordering) where
  compare_self := by
    intro a
    change compare (a.memory, a.addressSpace, a.regs) (a.memory, a.addressSpace, a.regs) = Ordering.eq
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} h := by
    change compare (a.memory, a.addressSpace, a.regs) (b.memory, b.addressSpace, b.regs) = Ordering.eq at h
    have hfields : (a.memory, a.addressSpace, a.regs) = (b.memory, b.addressSpace, b.regs) :=
      Std.LawfulEqCmp.eq_of_compare h
    cases a
    cases b
    simp at hfields
    simp [hfields]

/--
A decidable proposition as to weather an architecture state satisfies
ther termination condition.
-/
def ArchState.has_terminated (termCond : TerminationCondition nThreads)
    (s : ArchState nThreads) : Prop :=
  ∀ tid : Fin nThreads, termCond tid s.regs[tid]
deriving Decidable

/--
The result type returned from an architecture concurrency model after a termination condition.
-/
inductive ModelResult (nThreads : Nat) (Flag : Type) (termCond : TerminationCondition nThreads)
  /- A final state comes with a proof its terminated. -/
  | finalState (s : ArchState nThreads) (t : s.has_terminated termCond)
  | flagged (f : Flag)
  | error (msg : String)
deriving DecidableEq, Hashable


-- TODO: non-computational model definition.

def ComputationalTerminatingModel :=
  (nThreads : Nat) → (termCond : TerminationCondition nThreads) →
  ArchState nThreads → ListSet (ModelResult nThreads Unit termCond)

def ComputationalTerminatingModel.weaker
    (m₁ m₂ : ComputationalTerminatingModel) : Prop :=
  ∀ (nThreads : Nat) (termCond : TerminationCondition nThreads)
    (init final : ArchState nThreads) (t : final.has_terminated termCond),
  ∀ r ∈ (m₁ nThreads termCond init),
    r = ModelResult.finalState final t →
    r ∈ (m₂ nThreads termCond init)

def ComputationalTerminatingModel.weaker_refl {m : ComputationalTerminatingModel}
    : (m.weaker m)
  := by
  simp only [weaker]
  intros
  assumption

def ComputationalTerminatingModel.weaker_transitive
    {a b c : ComputationalTerminatingModel}
    : (a.weaker b) → (b.weaker c) → (a.weaker c)
  := by
  intro h₁ h₂
  rw [ComputationalTerminatingModel.weaker] at *
  intro nThreads termCond init final t r h₁' h_eq
  specialize h₁ nThreads termCond init final t r
  specialize h₂ nThreads termCond init final t r
  exact h₂ (h₁ h₁' h_eq) h_eq

end ArchSem.TerminatingModel

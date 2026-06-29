-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Std.Data.ExtTreeSet
import ArchSem.Trace
import Sail.ArchSem
import ArchSem.Defs
import ArchSem.TerminatingModel

/-!
This file defines architecture-generic machinery for defining axiomatic
memory consistency models.
-/

open Sail.ArchSem
open ArchSem.TerminatingModel

namespace ArchSem.CandidateExecutions

/-
The axiomatic models are currently based on relations built using an ExtTreeSet
from the standard library. This type was chosen as it is extensional and
elements can be enumerated.

The functions in this section are helper functions on the ExtTreeSet that should
probably be in the standard library but are not.

TODO: move these ExtTreeSet functions into the standard library or into a
more sensible locatio.
-/
section TreeSetHelpers

def subset {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Std.ExtTreeSet α cmp) : Prop :=
  ∀ (a : α), a ∈ r₁ → a ∈ r₂

instance {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (r₁ r₂ : Std.ExtTreeSet α cmp)
    : Decidable (subset r₁ r₂) := by
  if h : r₁.toList.all (fun a => decide (a ∈ r₂)) = true then
    apply Decidable.isTrue
    intro a h_mem
    have h_all := List.all_eq_true.mp h a (Std.ExtTreeSet.mem_toList.mpr h_mem)
    simpa using h_all
  else
    apply Decidable.isFalse
    intro h_subset
    apply h
    apply List.all_eq_true.mpr
    intro a h_mem
    have h_mem' := Std.ExtTreeSet.mem_toList.mp h_mem
    exact decide_eq_true (h_subset a h_mem')

instance {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]
    : HasSubset (Std.ExtTreeSet α cmp) where
  Subset := subset

instance {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (r₁ r₂ : Std.ExtTreeSet α cmp)
    : Decidable (HasSubset.Subset r₁ r₂) := by
  change Decidable (subset r₁ r₂)
  infer_instance

instance {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (s : Std.ExtTreeSet α cmp) (p : α → Prop)
    [DecidablePred p] : Decidable (∀ x ∈ s, p x) := by
  if h : s.toList.all (fun x => decide (p x)) = true then
    apply Decidable.isTrue
    intro x h_mem
    exact of_decide_eq_true (List.all_eq_true.mp h x (Std.ExtTreeSet.mem_toList.mpr h_mem))
  else
    apply Decidable.isFalse
    intro h_forall
    apply h
    apply List.all_eq_true.mpr
    intro x h_mem
    exact decide_eq_true (h_forall x (Std.ExtTreeSet.mem_toList.mp h_mem))

/--
Compute a cartesian set product.
-/
def setProd {cmp : α → α → Ordering} [Std.TransCmp cmp]
    {cmp' : α × α → α × α → Ordering} [Std.TransCmp cmp']
    (a b : Std.ExtTreeSet α cmp) : Std.ExtTreeSet (α × α) cmp' :=
  a.foldl (fun prod a =>
    b.foldl (fun prod b =>
      prod.insert (a, b)
    ) prod
  ) Std.ExtTreeSet.empty

end TreeSetHelpers

/-- The binray relation type used for axiomatic models. -/
abbrev Rel (α : Type) (cmp : α × α → α × α → Ordering := by exact compare)
  := Std.ExtTreeSet (α × α) cmp

namespace Rel

/-- Set-wise union of binary relations. -/
def union {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  Std.ExtTreeSet.union r₁ r₂

/-- Set-wise intersection of binary relations. -/
def inter {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  Std.ExtTreeSet.inter r₁ r₂

/-- Set-wise difference of binary relations. -/
def diff {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  Std.ExtTreeSet.diff r₁ r₂

/-- Construct a diagonal binary relation from a set. i.e. `{(x, x) | ∀ x ∈ S}`. -/
def diag {α : Type} {cmp' : α → α → Ordering} [Std.TransCmp cmp']
    {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (s : Std.ExtTreeSet α cmp') : Rel α cmp :=
  s.foldl (fun acc x => acc.insert (x, x)) Std.ExtTreeSet.empty

/-- Compute the transitive closure of a relation. i.e. `R⁺`. -/
def transitiveClosure {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Rel α cmp :=
  let lA := r.toList.foldr (fun (x, y) acc => x :: y :: acc) []
  lA.foldr
    (fun k s =>
      lA.foldl
        (fun s i =>
          lA.foldl
            (fun s j =>
              if s.contains (i, k) && s.contains (k, j) then s.insert (i, j) else s
            ) s
        ) s
    ) r

-- TODO: use maps to make `seq` faster.
/-- Sequencing of binray relations. -/
def seq {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    [DecidableEq α] (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  r₁.foldl (fun acc (x, y) =>
    r₂.foldl (fun acc (y', z) =>
      if y = y' then acc.insert (x, z) else acc
    ) acc
  ) Std.ExtTreeSet.empty

/-- Reversing all arrows in a binary relation. -/
def inv {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Rel α cmp :=
  r.foldl (fun acc (x, y) => acc.insert (y, x)) Std.ExtTreeSet.empty

instance {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    : Inv (Rel α cmp) where
  inv := inv

/-- Custom notation for manipulating binary relations.  -/
infixl:66 " ; " => seq
prefix:75 "Δ" => diag
postfix:76 "⁺" => transitiveClosure

/-- Proposition for weather a binary realtion is injective. -/
def injective {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Prop :=
  ∀ (x y z : α), (x, z) ∈ r → (y, z) ∈ r → x = y

instance {α : Type} {cmp : α × α → α × α → Ordering}
    [DecidableEq α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    (r : Rel α cmp) : Decidable (injective r) := by
  if h : r.toList.all (fun arrow₁ =>
      r.toList.all (fun arrow₂ => decide (arrow₁.snd = arrow₂.snd → arrow₁.fst = arrow₂.fst))) = true then
    apply Decidable.isTrue
    intro x y z h_xz h_yz
    have h_outer := List.all_eq_true.mp h (x, z) (Std.ExtTreeSet.mem_toList.mpr h_xz)
    have h_inner := List.all_eq_true.mp h_outer (y, z) (Std.ExtTreeSet.mem_toList.mpr h_yz)
    exact (of_decide_eq_true h_inner) rfl
  else
    apply Decidable.isFalse
    intro h_injective
    apply h
    apply List.all_eq_true.mpr
    intro arrow₁ h_arrow₁
    apply List.all_eq_true.mpr
    intro arrow₂ h_arrow₂
    cases arrow₁ with
    | mk x z =>
      cases arrow₂ with
      | mk y z' =>
        apply decide_eq_true
        intro h_z
        subst h_z
        exact h_injective x y z (Std.ExtTreeSet.mem_toList.mp h_arrow₁) (Std.ExtTreeSet.mem_toList.mp h_arrow₂)

/-- Proposition for weather a binary realtion is transitive. -/
def transitive {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Prop :=
  ∀ (x y z : α), (x, y) ∈ r → (y, z) ∈ r → (x, z) ∈ r

instance {α : Type} {cmp : α × α → α × α → Ordering}
    [DecidableEq α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] (r : Rel α cmp)
    : Decidable (transitive r) := by
  if h : r.toList.all (fun arrow₁ =>
      r.toList.all (fun arrow₂ => decide (arrow₁.snd = arrow₂.fst → (arrow₁.fst, arrow₂.snd) ∈ r))) = true then
    apply Decidable.isTrue
    intro x y z h_xy h_yz
    have h_outer := List.all_eq_true.mp h (x, y) (Std.ExtTreeSet.mem_toList.mpr h_xy)
    have h_inner := List.all_eq_true.mp h_outer (y, z) (Std.ExtTreeSet.mem_toList.mpr h_yz)
    exact (of_decide_eq_true h_inner) rfl
  else
    apply Decidable.isFalse
    intro h_transitive
    apply h
    apply List.all_eq_true.mpr
    intro arrow₁ h_arrow₁
    apply List.all_eq_true.mpr
    intro arrow₂ h_arrow₂
    cases arrow₁ with
    | mk x y =>
      cases arrow₂ with
      | mk y' z =>
        apply decide_eq_true
        intro h_y
        change y = y' at h_y
        subst h_y
        exact h_transitive x y z (Std.ExtTreeSet.mem_toList.mp h_arrow₁) (Std.ExtTreeSet.mem_toList.mp h_arrow₂)

/-- Proposition for weather a binary realtion is irreflexive. -/
def irreflexive {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Prop :=
  ∀ (x : α), (x, x) ∉ r

instance {α : Type} {cmp : α × α → α × α → Ordering}
    [DecidableEq α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    (r : Rel α cmp) : Decidable (irreflexive r) := by
  if h : r.toList.all (fun arrow => decide (arrow.fst ≠ arrow.snd)) = true then
    apply Decidable.isTrue
    intro x h_xx
    have h_ne := List.all_eq_true.mp h (x, x) (Std.ExtTreeSet.mem_toList.mpr h_xx)
    exact (of_decide_eq_true h_ne) rfl
  else
    apply Decidable.isFalse
    intro h_irreflexive
    apply h
    apply List.all_eq_true.mpr
    intro arrow h_arrow
    cases arrow with
    | mk x y =>
      apply decide_eq_true
      intro h_xy
      change x = y at h_xy
      subst h_xy
      exact h_irreflexive x (Std.ExtTreeSet.mem_toList.mp h_arrow)

/-- Proposition for weather a binary realtion is acyclic. -/
def acyclic {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r : Rel α cmp) : Prop :=
  r⁺.irreflexive

instance {α : Type} {cmp : α × α → α × α → Ordering}
    [DecidableEq α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    (r : Rel α cmp) : Decidable (acyclic r) := by
  rw [acyclic]
  infer_instance

/-- Get the domain of a binray relation. -/
def domain {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
  {cmp' : α → α → Ordering} [Std.TransCmp cmp']
  (r : Rel α cmp) : Std.ExtTreeSet α cmp' :=
  r.foldr (fun (x,_) s => s.insert x) Std.ExtTreeSet.empty

/-- Get the range of a binray relation. -/
def range {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
  {cmp' : α → α → Ordering} [Std.TransCmp cmp']
  (r : Rel α cmp) : Std.ExtTreeSet α cmp' :=
  r.foldr (fun (_,y) s => s.insert y) Std.ExtTreeSet.empty

end Rel

/-- An "Instruction Monad" encoding ISA semantics. -/
abbrev IMon [Arch] := FreeM (InstructionEffect ⊕ FinChoice)

/--
An "Instruction Event" representing an instruction effect paired with its
return value.
-/
def IEvent [Arch] : Type := FreeM.Event InstructionEffect

/--
An "Instruction Trace" representing a (possibly partial) recording of the
execution of an instruction.
-/
def ITrace [Arch] : Type → Type := FreeM.Trace InstructionEffect

namespace IEvent

variable [Arch]

/- Helper functions for getting information about an `IEvent`. -/

def getReg (ev : IEvent) : Option Arch.register :=
  match ev.call with
  | .regRead reg _ => .some reg
  | .regWrite reg _ _ => .some reg
  | _ => .none


def getRegValue (ev : IEvent)
    : Option (Σ (r : Arch.register), Arch.register_type r) :=
  match h : ev.call with
  | .regRead reg _ =>
    have h_eq : Arch.register_type reg = InstructionEffect.ret ev.call := by
      simp [InstructionEffect.ret, h]
    let val : Arch.register_type reg := h_eq ▸ ev.ret
    .some ⟨reg, val⟩
  | .regWrite reg _ val => .some ⟨reg, val⟩
  | _ => .none

def getMemRequest (ev : IEvent) : Option MemRequest :=
  match ev.call with
  | .memRead memReq => .some memReq
  | .memWriteAnnounce memReq => .some memReq
  | .memWrite memReq _ _ => .some memReq
  | _ => .none

def getAddr (ev : IEvent) : Option Address := do
  let memReq ← ev.getMemRequest
  return memReq.address

def getSize (ev : IEvent) : Option Nat := do
  let memReq ← ev.getMemRequest
  return memReq.size

def getMemValue (ev : IEvent) : Option (Σ n : Nat, BitVec (8 * n)) :=
  match h : ev.call with
  | .memRead req =>
    have h_eq : Except Arch.abort (BitVec (8 * req.size) × BitVec req.numTag) = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    match (h_eq ▸ ev.ret) with
    | Except.ok (val, _) => .some ⟨req.size, val⟩
    | Except.error _ => .none
  | .memWrite req val _ => .some ⟨req.size, val⟩
  | _ => .none

def getBarrier (ev : IEvent) : Option Arch.barrier :=
  match ev.call with
  | .barrier barrier => .some barrier
  | _ => .none

def getCacheOp (ev : IEvent) : Option Arch.cache_op :=
  match ev.call with
  | .cacheOp op => .some op
  | _ => .none

def getTlbi (ev : IEvent) : Option Arch.tlbi :=
  match ev.call with
  | .tlbOp tlbi => .some tlbi
  | _ => .none

def getTransStart (ev : IEvent) : Option Arch.trans_start :=
  match ev.call with
  | .translationStart ts => .some ts
  | _ => .none

def getTransEnd (ev : IEvent) : Option Arch.trans_end :=
  match ev.call with
  | .translationEnd te => .some te
  | _ => .none

section IsReg

variable (p : (r : Arch.register) → Option Arch.sys_reg_id → Arch.register_type r → Prop) (ev : IEvent)

def is_reg_read_with : Prop
  := match h : ev.call with
  | .regRead reg racc =>
    have h_eq : Arch.register_type reg = InstructionEffect.ret ev.call := by
      simp [InstructionEffect.ret, h]
    let val : Arch.register_type reg := h_eq ▸ ev.ret
    p reg racc val
  | _ => False

instance [h : ∀ r acc v, Decidable (p r acc v)] : Decidable (is_reg_read_with p ev) := by
  rw [is_reg_read_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_reg_write_with : Prop
  := match ev.call with
  | .regWrite reg racc val => p reg racc val
  | _ => False

instance [h : ∀ r acc v, Decidable (p r acc v)] : Decidable (is_reg_write_with p ev) := by
  rw [is_reg_write_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_reg_event_with : Prop := is_reg_read_with p ev ∨ is_reg_write_with p ev

end IsReg

def is_mem_read_req_with
    (p : (req : MemRequest) → Except Arch.abort (BitVec (8 * req.size) × BitVec (req.numTag)) → Prop)
    (ev : IEvent)
  := match h : ev.call with
  | .memRead req =>
    let h_eq : Except Arch.abort (BitVec (8 * req.size) × BitVec req.numTag) = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    p req (h_eq ▸ ev.ret)
  | _ => False

instance [h : ∀ req res, Decidable (p req res)] : Decidable (is_mem_read_req_with p ev) := by
  rw [is_mem_read_req_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_read_with
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Prop)
    : IEvent → Prop
  := is_mem_read_req_with (fun req res => match res with
       | .ok val => p req val.fst val.snd
       | .error _ => False)

instance [h : ∀ req val tags, Decidable (p req val tags)]
    : Decidable (is_mem_read_with p ev) := by
  rw [is_mem_read_with, is_mem_read_req_with] ; split
  · split
    · apply h
    · exact Decidable.isFalse False.elim
  · exact Decidable.isFalse False.elim

def is_mem_write_announce_with (p : MemRequest → Prop) (ev : IEvent) :=
  match ev.call with
  | .memWriteAnnounce req => p req
  | _ => False

instance [h : ∀ req, Decidable (p req)] : Decidable (is_mem_write_announce_with p ev) := by
  rw [is_mem_write_announce_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_write_req_with
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Except Arch.abort Unit → Prop)
    (ev : IEvent) : Prop
  := match h : ev.call with
  | .memWrite req val tags =>
    let h_eq : Except Arch.abort Unit = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    p req val tags (h_eq ▸ ev.ret)
  | _ => False

instance [h : ∀ req val tags res, Decidable (p req val tags res)]
    : Decidable (is_mem_write_req_with p ev) := by
  rw [is_mem_write_req_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_write_with
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Prop)
    : IEvent → Prop
  := is_mem_write_req_with (fun req val tags res => match res with
       | .ok () => p req val tags
       | .error _ => False)

instance [h : ∀ req val tags, Decidable (p req val tags)]
    : Decidable (is_mem_write_with p ev) := by
  rw [is_mem_write_with, is_mem_write_req_with] ; split
  · split
    · apply h
    · exact Decidable.isFalse False.elim
  · exact Decidable.isFalse False.elim

def is_barrier_with (p : Arch.barrier → Prop) (ev : IEvent) : Prop
  := match ev.call with
  | .barrier barrier => p barrier
  | _ => False

instance [h : ∀ barrier, Decidable (p barrier)]
    : Decidable (is_barrier_with p ev) := by
  rw [is_barrier_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_cache_op_with (p : Arch.cache_op → Prop) (ev : IEvent) : Prop
  := match ev.call with
  | .cacheOp op => p op
  | _ => False

instance [h : ∀ op, Decidable (p op)]
    : Decidable (is_cache_op_with p ev) := by
  rw [is_cache_op_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_tlb_op_with (p : Arch.tlbi → Prop) (ev : IEvent) : Prop
  := match ev.call with
  | .tlbOp op => p op
  | _ => False

instance [h : ∀ op, Decidable (p op)]
    : Decidable (is_tlb_op_with p ev) := by
  rw [is_tlb_op_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_arch_exception (ev : IEvent) : Prop
  := match ev.call with
  | .archException _ => True
  | _ => False

instance : Decidable (is_arch_exception ev) := by
  rw [is_arch_exception]
  split <;> infer_instance

def is_return_exception (ev : IEvent) : Prop
  := match ev.call with
  | .returnExecption => True
  | _ => False

instance : Decidable (is_return_exception ev) := by
  rw [is_return_exception]
  split <;> infer_instance

abbrev is_reg_read (ev : IEvent) := is_reg_read_with (fun _ _ _ => True) ev
abbrev is_reg_write (ev : IEvent) := is_reg_write_with (fun _ _ _ => True) ev
abbrev is_reg_event (ev : IEvent) := is_reg_event_with (fun _ _ _ => True) ev
abbrev is_mem_read_req (ev : IEvent) := is_mem_read_req_with (fun _ _ => True) ev
abbrev is_mem_read (ev : IEvent) := is_mem_read_with (fun _ _ _ => True) ev
abbrev is_mem_write_announce (ev : IEvent) := is_mem_write_announce_with (fun _ => True) ev
abbrev is_mem_write_req (ev : IEvent) := is_mem_write_req_with (fun _ _ _ _ => True) ev
abbrev is_mem_write (ev : IEvent) := is_mem_write_with (fun _ _ _ => True) ev
abbrev is_barrier (ev : IEvent) := is_barrier_with (fun _ => True) ev
abbrev is_cache_op (ev : IEvent) := is_cache_op_with (fun _ => True) ev
abbrev is_tlb_op (ev : IEvent) := is_tlb_op_with (fun _ => True) ev

def is_unsupported_event (ev : IEvent) : Prop :=
  is_mem_read_req_with (fun req _ => req.numTag ≠ 0) ev ∨
  is_mem_write_req_with (fun req _ _ _ => req.numTag ≠ 0) ev

instance : Decidable (is_unsupported_event ev) := by
  unfold is_unsupported_event
  infer_instance

end IEvent

/--
Proposition for weather the trace could have been produced from a particular
ISA.
-/
inductive ITrace.matches_isa [Arch]
    : IMon α → ITrace α → Prop
  | stopped (f : FreeM (InstructionEffect ⊕ FinChoice) α) : matches_isa f .stopped
  | ret (a : α) : matches_isa (.pure a) (.ret a)
  | eff (eff : InstructionEffect) (k : eff.ret → FreeM (InstructionEffect ⊕ FinChoice) α)
      : matches_isa (.impure (.inl eff) k) (.openCall eff)
  | next (eff : InstructionEffect) (k : eff.ret → IMon α) (ret : eff.ret)
      (t : ITrace α)
      : matches_isa (k ret) t → matches_isa (.impure (.inl eff) k) (.cons (eff &→ ret) t)
  | choose (n : Nat) (i : Fin n) (k : Fin n → IMon α) (t : ITrace α)
      : matches_isa (k i) t → matches_isa (.impure (.inr n) k) t

/-- An index to an event from some instruction Event from some thread. -/
structure Eid where
  /-- Thread ID. -/
  tid : Nat
  /-- Instruction ID. -/
  iid : Nat
  /-- Instruction Event ID. -/
  ieid : Nat
deriving DecidableEq

/-- Defined an ordering on Eid so they can be stored in TreeMap. -/
def Eid.compare (a b : Eid) : Ordering :=
  (Ord.compare : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Ordering)
    (a.tid, a.iid, a.ieid) (b.tid, b.iid, b.ieid)

instance : Ord Eid where
  compare := Eid.compare

instance : Std.TransCmp Eid.compare where
  isLE_trans := by
    intro a b c hab hbc
    simpa only [Eid.compare] using
      (Std.TransCmp.isLE_trans
        (cmp := (Ord.compare : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Ordering)) hab hbc)
  eq_swap := by
    intro a b
    simpa only [Eid.compare] using
      (Std.OrientedCmp.eq_swap
        (cmp := (Ord.compare : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Ordering))
        (a := (a.tid, a.iid, a.ieid)) (b := (b.tid, b.iid, b.ieid)))

instance : Std.LawfulEqCmp Eid.compare where
  compare_self := by
    intro a
    simpa only [Eid.compare] using
      (Std.ReflCmp.compare_self
        (cmp := (Ord.compare : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Ordering))
        (a := (a.tid, a.iid, a.ieid)))
  eq_of_compare := by
    intro a b h
    have h_key : (a.tid, a.iid, a.ieid) = (b.tid, b.iid, b.ieid) := by
      apply Std.LawfulEqCmp.eq_of_compare
        (cmp := (Ord.compare : (Nat × Nat × Nat) → (Nat × Nat × Nat) → Ordering))
      simpa only [Eid.compare] using h
    cases a
    cases b
    simp_all

instance : Std.TransCmp (compare : Eid → Eid → Ordering) := by
  change Std.TransCmp Eid.compare
  infer_instance

instance : Std.LawfulEqCmp (compare : Eid → Eid → Ordering) := by
  change Std.LawfulEqCmp Eid.compare
  infer_instance

/--
A pre-candidate-execution is the recording of events from all threads without
additional information such as coherence.
-/
structure PreCand [Arch] [ArchExtra] (nThreads : Nat) where
  init : ArchState nThreads
  events : Vector (List (ITrace Unit)) nThreads

namespace PreCand

variable [Arch] [ArchExtra]

/--
Could the pre-candidate-execution's instruction traces have been produced from
an ISA.
-/
def matches_isa (p : PreCand nThreads) (isem : IMon Unit) : Prop :=
  ∀ (tid : Fin nThreads), ∀ trace ∈ p.events[tid], trace.matches_isa isem

/--
Are all the instruction traces complete.
-/
def is_complete (p : PreCand nThreads) : Prop :=
  ∀ (tid : Fin nThreads), ∀ trace ∈ p.events[tid], trace.snd = .ret ()

/-- Find an instruction trace from a thread and instruction id. -/
def lookupInstruction (p : PreCand nThreads) (tid iid : Nat)
    : Option (ITrace Unit) := do
  let threadTraces ← p.events[tid]?
  threadTraces[iid]?

/-- Get a list of all instructions indexed by their thread and instruction id. -/
def instructionList (p : PreCand nThreads) : List (Nat × Nat × ITrace Unit) :=
  p.events.toList.mapIdx
    (fun tid traces => traces.mapIdx (fun iid trace => (tid, iid, trace)))
  |>.flatten

-- TODO: prove
theorem lookup_instruction_list (p : PreCand nThreads) (tid iid : Nat) (t : ITrace Unit)
    : lookupInstruction p tid iid = .some t ↔ (tid, iid, t) ∈ instructionList p := by
  sorry

/-- Find an instruction event from its index. -/
def lookupIEvent (p : PreCand nThreads) (tid iid ieid : Nat) : Option IEvent := do
  let inst ← p.lookupInstruction tid iid
  inst.fst[ieid]?

/-- Get a list of all instruction events paired with their index. -/
def iEventList (p : PreCand nThreads) : List (Nat × Nat × Nat × IEvent) :=
  p.instructionList.map
    (fun (tid, iid, trace) => trace.fst.mapIdx (fun ieid ev => (tid, iid, ieid, ev)))
  |>.flatten

-- TODO: prove
theorem lookup_ievent_list (p : PreCand nThreads) (tid iid ieid : Nat) (ev : IEvent)
    : lookupIEvent p tid iid ieid = .some ev ↔ (tid, iid, ieid, ev) ∈ p.iEventList := by
  sorry

/-- Get a list of all instruction events paired with their index. -/
def iEventList' (p : PreCand nThreads) : List (Eid × IEvent) :=
  p.iEventList |>.map (fun (tid, iid, ieid, ev) => ({tid, iid, ieid}, ev))

/-- Does an Eid point to a valid instruction event. -/
def eid_valid (p : PreCand nThreads) (eid : Eid) : Prop :=
  (lookupIEvent p eid.tid eid.iid eid.ieid).isSome

instance (p : PreCand nThreads) (eid : Eid) : Decidable (eid_valid p eid) := by
  simp [eid_valid]
  infer_instance

instance : GetElem (PreCand nThreads) Eid IEvent eid_valid where
   getElem (p : PreCand nThreads) (eid : Eid) (h : eid_valid p eid) : IEvent := by
     match h_lookup : lookupIEvent p eid.tid eid.iid eid.ieid with
     | .some ev => exact ev
     | .none =>
       rw [eid_valid] at h
       rw [←Option.not_isSome_iff_eq_none] at h_lookup
       contradiction

/-- Get the Eid of all instructions that match the proposition. -/
def collectEidWith (f : Eid → IEvent → Prop) (p : PreCand nThreads)
    [h : ∀ eid ev, Decidable (f eid ev)]
    : Std.ExtTreeSet Eid :=
  Std.ExtTreeSet.ofList (
    p.iEventList'
    |>.filter (fun (eid, event) => f eid event)
    |>.map Prod.fst
  )

/-- Get a set of all valid eid. -/
def eids (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ _ => True)

/- Helper functions for getting event id's. -/

def regReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_reg_read ev)
def pcReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_reg_read_with (fun reg _ _ => reg = ArchExtra.register_pc) ev)

def regWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_reg_write ev)
def pcWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_reg_write_with (fun reg _ _ => reg = ArchExtra.register_pc) ev)

def memReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_read ev)
def memReadReqs (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_read_req ev)

def memReadAborts (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_read_req_with (fun _ res => not res.isOk) ev)

def memWriteAddrAnnounces (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_write_announce ev)
def memWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_write ev)
def memWriteReqs (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_write_req ev)
def memWriteAborts (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_write_req_with (fun _ _ _ res => not res.isOk) ev)

def memEvents (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.memReads ∪ p.memWrites

def readsByKind (p : PreCand nThreads) (q : Arch.mem_acc → Bool)
    : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_read_with (fun req _ _ => q req.accessKind) ev)
def writesByKind (p : PreCand nThreads) (q : Arch.mem_acc → Bool)
    : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_mem_write_with (fun req _ _ => q req.accessKind) ev)

def barriers (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_barrier ev)
def cacheOps (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_cache_op ev)
def tlbOps (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun _ ev => IEvent.is_tlb_op ev)

/--
Get the register map that a thread will have after execution all the
instructions in its trace.
-/
def finalThreadRegisterMap (p : PreCand nThreads) (tid : Fin nThreads) : RegisterMap :=
  p.events[tid].foldl (fun regMap iTrace =>
    iTrace.fst.foldl (fun regMap event =>
      match event.call with
      | .regWrite reg _acc val =>
        -- TODO (think about): the operational models are able to throw an error
        -- here when there is an invalid access type.
        regMap.insert reg val
      | _ => regMap
    ) regMap
  )
  p.init.regs[tid]

/--
Get final register states for every thread.
-/
def finalRegisterMaps (p : PreCand nThreads) : Vector RegisterMap nThreads :=
  Vector.ofFn (finalThreadRegisterMap p)

/--
Partition all event ids by `getKey` and return them grouped by the key.
-/
def collectEidByKey {K : Type} [Ord K] [Std.TransCmp (compare : K → K → Ordering)]
    (p : PreCand nThreads) (getKey : Eid → IEvent → Option K)
    : Std.ExtTreeMap K (Std.ExtTreeSet Eid) :=
  p.iEventList'.foldl (fun map (eid, event) =>
      match getKey eid event with
      | .some key => map.insert key ((map.getD key (Std.ExtTreeSet.empty (cmp := Eid.compare))).insert eid)
      | .none => map
    ) Std.ExtTreeMap.empty

/--
Get a binary relation which relates any two events that map to the same key
according the `getKey`.
-/
def sameKey {K : Type} [Ord K] [Std.TransCmp (compare : K → K → Ordering)]
    (p : PreCand nThreads) (getKey : Eid → IEvent → Option K)
    : Rel Eid :=
  (collectEidByKey p getKey).foldl (fun acc _ eids =>
    Std.ExtTreeSet.union acc (setProd eids eids)
  ) Std.ExtTreeSet.empty

def sameThread (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid _ => .some eid.tid)

def sameInstructionInstance (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid _ => .some (eid.tid, eid.iid))

def intraInstructionOrder (p : PreCand nThreads) : Rel Eid :=
  p.sameInstructionInstance
  |>.filter (fun (a,b) => a.ieid < b.ieid)

def interInstructionOrder (p : PreCand nThreads) : Rel Eid :=
  p.sameThread
  |>.filter (fun (a,b) => a.iid < b.iid)

def programOrder (p : PreCand nThreads) : Rel Eid :=
  p.interInstructionOrder ∪ p.intraInstructionOrder

def sameAddr (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun _ ev => ev.getAddr)

def sameSize (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun _ ev => ev.getSize)

def sameFootprint (p : PreCand nThreads) : Rel Eid :=
  p.sameAddr ∩ p.sameSize

def sameMemValue (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun _ ev => ev.getMemValue)

def sameReg (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid ev => Option.map (eid.tid, ·) ev.getReg)

def sameRegSameValue (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid ev => Option.map (eid.tid, ·) ev.getRegValue)

/--
Is this event a register read read who's value read is consistent with
initial register states.
-/
def is_valid_init_reg_read (p : PreCand nThreads) (eid : Eid) : Prop :=
  match p[eid]? with
  | .some ev =>
      if h : eid.tid < nThreads then
        let tid : Fin nThreads := ⟨eid.tid, h⟩
        ev.is_reg_read_with (fun reg _acc val =>
          p.init.regs[tid].get? reg = Option.some val)
      else
        False
  | .none => False

instance : Decidable (is_valid_init_reg_read p eid) := by
  unfold is_valid_init_reg_read
  split <;> infer_instance

def possibleInitRegReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEidWith (fun eid _ev => p.is_valid_init_reg_read eid)

def is_valid_init_mem_read (p : PreCand nThreads) (eid : Eid) : Prop :=
  match p[eid]? with
  | .some ev => ev.is_mem_read_with (fun req val _tags =>
      p.init.memory.read req.size req.address = val
    )
  | .none => False

instance : Decidable (is_valid_init_mem_read p eid) := by
  unfold is_valid_init_mem_read
  split <;> infer_instance

-- TODO: `not_after` relation. pair is in this iff `(· ∩ po⁻¹ = ∅)`.

end PreCand

/-- A candidate execution. -/
structure Cand (nThreads : Nat) [Arch] [ArchExtra] where
  pre : PreCand nThreads
  memReadsFrom : Rel Eid
  regReadsFrom : Rel Eid
  coherence : Rel Eid
  exclusives : Rel Eid

namespace Cand

variable [Arch] [ArchExtra]

/-- Does the event id point to a valid event. -/
def eid_valid (c : Cand nThreads) : Eid → Prop := c.pre.eid_valid

instance (c : Cand nThreads) (eid : Eid) : Decidable (eid_valid c eid) := by
  simp [eid_valid]
  infer_instance

instance : GetElem (Cand nThreads) Eid IEvent eid_valid where
  getElem (c : Cand nThreads) (eid : Eid) (valid : c.eid_valid eid) : IEvent
    := c.pre[eid]

/--
Get the last write to each location in the candidate exeuctions instruction
traces.
-/
def finalWrites (c : Cand nThreads) : Std.ExtTreeMap Address (Eid × BitVec 8) :=
  c.pre.iEventList'.foldl (fun mem (eid, ev) =>
    match ev.call with
    | .memWrite req val tags =>
      (List.finRange req.size).foldl (fun mem (i : Fin req.size) =>
        -- CR clang for thibaut: What happens if this addition overflows?
        let addr := req.address + i.val
        let byte := (Sail.bitvec_to_vecbytes val)[i]
        match mem.get? addr with
        | .some (eid', byte') =>
          if c.coherence.contains (eid, eid')
          then mem.insert addr (eid, byte)
          else mem
        | .none => mem.insert addr (eid, byte)
      ) mem
    | _ => mem
  ) Std.ExtTreeMap.empty

/--
Get the final memory map after execution all instruction traces.
-/
def finalMemMap (c : Cand nThreads) : MemoryMap :=
  let writtenMem := (finalWrites c).map (fun _ (_,v) => v)
  Std.ExtTreeMap.union c.pre.init.memory writtenMem

/--
Get the final architecture state after a candidate execution.
-/
def toArchState (c : Cand nThreads) : ArchState nThreads :=
  { memory := c.finalMemMap
  , addressSpace := c.pre.init.addressSpace
  , regs := c.pre.finalRegisterMaps
  }

def initMemReads (c : Cand nThreads) : Std.ExtTreeSet Eid :=
  c.pre.memReads \ c.memReadsFrom.range

def memFromReads (c : Cand nThreads) : Rel Eid :=
  (Δ c.pre.memReads ; c.pre.sameAddr ; Δ c.pre.memWrites)
    \ ((c.coherence ∪ Δ c.pre.memWrites) ; c.memReadsFrom)⁻¹

def initRegReads (c : Cand nThreads) : Std.ExtTreeSet Eid :=
  c.pre.regReads \ c.regReadsFrom.range

def regFromReads (c : Cand nThreads) : Rel Eid :=
  Δ c.pre.regReads ; c.pre.sameReg ; Δ c.pre.regWrites
    \ ((c.pre.interInstructionOrder ∪ Δ c.pre.regWrites) ; c.regReadsFrom)⁻¹

def pcReadsFrom (c : Cand nThreads) : Rel Eid :=
  Δ c.pre.pcWrites ; c.regReadsFrom ; Δ c.pre.pcReads

def regReadsFromData (c : Cand nThreads) : Rel Eid :=
  c.regReadsFrom \ c.pcReadsFrom

def is_valid_mem_rf_data (c : Cand nThreads) (wsrc rdst : Eid) : Prop :=
  match (do
      let write ← c[wsrc]?
      let wAddr ← write.getAddr
      let wVal ← write.getMemValue
      let read ← c[rdst]?
      let rAddr ← read.getAddr
      let rVal ← read.getMemValue
      return (wAddr, wVal, rAddr, rVal)
    ) with
  | .some (wAddr, wVal, rAddr, rVal) =>
    wAddr = rAddr ∧ wVal = rVal
  | .none => False

instance : Decidable (is_valid_mem_rf_data c wsrc rdst) := by
  unfold is_valid_mem_rf_data
  split <;> infer_instance

structure mem_reads_from_wf (c : Cand nThreads) where
  from_writes : c.memReadsFrom.domain ⊆ c.pre.memWrites
  to_reads : c.memReadsFrom.range ⊆ c.pre.memReads
  injective : c.memReadsFrom.injective
  data_valid : ∀ arrow ∈ c.memReadsFrom, c.is_valid_mem_rf_data arrow.fst arrow.snd
  initial_data_valid : ∀ eid ∈ c.initMemReads, c.pre.is_valid_init_mem_read eid

theorem mem_reads_from_wf.mk_iff (c : Cand nThreads)
    : mem_reads_from_wf c
    ↔ c.memReadsFrom.domain ⊆ c.pre.memWrites
    ∧ c.memReadsFrom.range ⊆ c.pre.memReads
    ∧ c.memReadsFrom.injective
    ∧ (∀ arrow ∈ c.memReadsFrom, c.is_valid_mem_rf_data arrow.fst arrow.snd)
    ∧ (∀ eid ∈ c.initMemReads, c.pre.is_valid_init_mem_read eid)
  := by
  apply Iff.intro
  · exact fun { from_writes, to_reads, injective, data_valid, initial_data_valid }
      => ⟨from_writes, to_reads, injective, data_valid, initial_data_valid⟩
  · exact fun ⟨from_writes, to_reads, injective, data_valid, initial_data_valid⟩
      => { from_writes, to_reads, injective, data_valid, initial_data_valid }

instance : Decidable (mem_reads_from_wf c) := by
  rw [mem_reads_from_wf.mk_iff]
  infer_instance

structure coherence_wf (c : Cand nThreads) where
  transitive : c.coherence.transitive
  irreflexive : c.coherence.irreflexive
  -- TODO: this differs from archsem-rocq. I'm confused in case weid1=weid2 in archsem-rocq.
  total_over_same_addr :
    ∀ arrow ∈ c.pre.sameAddr, arrow ∈ c.coherence ∨ arrow.swap ∈ c.coherence

theorem coherence_wf.mk_iff (c : Cand nThreads)
    : coherence_wf c ↔ c.coherence.transitive ∧ c.coherence.irreflexive ∧ (∀ arrow ∈ c.pre.sameAddr, arrow ∈ c.coherence ∨ arrow.swap ∈ c.coherence)
  := by
  apply Iff.intro
  · exact fun { transitive, irreflexive, total_over_same_addr }
      => ⟨transitive, irreflexive, total_over_same_addr⟩
  · exact fun ⟨transitive, irreflexive, total_over_same_addr⟩
      => { transitive, irreflexive, total_over_same_addr }

instance : Decidable (coherence_wf c) := by
  rw [coherence_wf.mk_iff]
  infer_instance

structure exclusives_wf (c : Cand nThreads) where
  from_reads : c.exclusives.domain ⊆ c.pre.readsByKind Arch.mem_acc_is_exclusive
  to_writes : c.exclusives.range ⊆ c.pre.writesByKind Arch.mem_acc_is_exclusive
  instruction_order : c.exclusives ⊆ c.pre.interInstructionOrder
  same_addr : c.exclusives ⊆ c.pre.sameAddr

/-
`mk_iff` can be derived automatically with a mathlib attribute but
we dont depend on mathlib.
-/
theorem exclusives_wf.mk_iff (c : Cand nThreads)
    : exclusives_wf c
    ↔ c.exclusives.domain ⊆ c.pre.readsByKind Arch.mem_acc_is_exclusive
    ∧ c.exclusives.range ⊆ c.pre.writesByKind Arch.mem_acc_is_exclusive
    ∧ c.exclusives ⊆ c.pre.interInstructionOrder
    ∧ c.exclusives ⊆ c.pre.sameAddr
  := by
  apply Iff.intro
  · exact fun { from_reads, to_writes, instruction_order, same_addr }
      => ⟨from_reads, to_writes, instruction_order, same_addr⟩
  · exact fun ⟨from_reads, to_writes, instruction_order, same_addr⟩
      => { from_reads, to_writes, instruction_order, same_addr }

instance : Decidable (exclusives_wf c) := by
  rw [exclusives_wf.mk_iff]
  infer_instance

structure reg_reads_from_wf (c : Cand nThreads) where
  from_writes : c.regReadsFrom.domain ⊆ c.pre.regWrites
  to_reads : c.regReadsFrom.range ⊆ c.pre.regReads
  injective : c.regReadsFrom.injective
  data_valid : c.regReadsFrom ⊆ c.pre.sameRegSameValue
  initial_data_valid : c.initRegReads ⊆ c.pre.possibleInitRegReads

theorem reg_reads_from_wf.mk_iff (c : Cand nThreads)
    : reg_reads_from_wf c
    ↔ c.regReadsFrom.domain ⊆ c.pre.regWrites
    ∧ c.regReadsFrom.range ⊆ c.pre.regReads
    ∧ c.regReadsFrom.injective
    ∧ c.regReadsFrom ⊆ c.pre.sameRegSameValue
    ∧ c.initRegReads ⊆ c.pre.possibleInitRegReads
  := by
  apply Iff.intro
  · exact fun { from_writes, to_reads, injective, data_valid, initial_data_valid }
      => ⟨from_writes, to_reads, injective, data_valid, initial_data_valid⟩
  · exact fun ⟨from_writes, to_reads, injective, data_valid, initial_data_valid⟩
      => { from_writes, to_reads, injective, data_valid, initial_data_valid }

instance : Decidable (reg_reads_from_wf c) := by
  rw [reg_reads_from_wf.mk_iff]
  infer_instance

def addr_space_wf (c : Cand nThreads) : Prop :=
  ∀ pair ∈ c.pre.iEventList',
    match pair.snd.getMemRequest with
    | .some req => req.addressSpace = c.pre.init.addressSpace
    | .none => True

instance : Decidable (addr_space_wf c) := by
  unfold addr_space_wf
  if h : c.pre.iEventList'.all (fun pair =>
      match pair.snd.getMemRequest with
      | .some req => decide (req.addressSpace = c.pre.init.addressSpace)
      | .none => true) = true then
    apply Decidable.isTrue
    intro pair h_pair
    have h_pair_valid := List.all_eq_true.mp h pair h_pair
    split at h_pair_valid
    · exact of_decide_eq_true h_pair_valid
    · exact True.intro
  else
    apply Decidable.isFalse
    intro h_wf
    apply h
    apply List.all_eq_true.mpr
    intro pair h_pair
    specialize h_wf pair h_pair
    cases h_req : pair.snd.getMemRequest with
    | some req =>
      simp [h_req] at h_wf ⊢
      exact h_wf
    | none =>
      rfl

-- TODO: `footprint_wf`. I dont understand why archsem rocq strictly needs this.

structure wf (c : Cand nThreads) where
  only_supported_events : ∀ pair ∈ c.pre.iEventList', ¬ pair.snd.is_unsupported_event
  addr_space : addr_space_wf c
  mem_reads_from : mem_reads_from_wf c
  coherence : coherence_wf c
  exclusives : exclusives_wf c
  reg_reads_from : reg_reads_from_wf c

theorem wf.mk_iff (c : Cand nThreads)
    : wf c
    ↔ (∀ pair ∈ c.pre.iEventList', ¬ pair.snd.is_unsupported_event)
    ∧ addr_space_wf c
    ∧ mem_reads_from_wf c
    ∧ coherence_wf c
    ∧ exclusives_wf c
    ∧ reg_reads_from_wf c
  := by
  apply Iff.intro
  · exact fun { only_supported_events, addr_space, mem_reads_from, coherence, exclusives, reg_reads_from }
      => ⟨only_supported_events, addr_space, mem_reads_from, coherence, exclusives, reg_reads_from⟩
  · exact fun ⟨only_supported_events, addr_space, mem_reads_from, coherence, exclusives, reg_reads_from⟩
      => { only_supported_events, addr_space, mem_reads_from, coherence, exclusives, reg_reads_from }

instance : Decidable (wf c) := by
  rw [wf.mk_iff]
  infer_instance

def intra_instruction_order_addr (c : Cand nThreads) : Rel Eid :=
  c.pre.intraInstructionOrder ;
  ((Δ c.pre.memWriteAddrAnnounces ; c.pre.intraInstructionOrder ; Δ c.pre.memWriteReqs
   ∩ c.pre.sameFootprint) ∪ Δ c.pre.memReads)

def addr (c : Cand nThreads) : Rel Eid :=
  Δ c.pre.memReads ;
  (Δ c.pre.memReads ∪ (c.pre.intraInstructionOrder ; c.regReadsFromData)⁺) ;
  c.pre.intraInstructionOrder ;
  Δ c.pre.memEvents


def data (c : Cand nThreads) : Rel Eid :=
  Δ c.pre.memReads ;
  (Δ c.pre.memReads ∪ (c.pre.intraInstructionOrder ; c.regReadsFromData)⁺) ;
  c.pre.intraInstructionOrder ;
  Δ c.pre.memWriteReqs

def ctrl (c : Cand nThreads) : Rel Eid :=
  Δ c.pre.memReads ;
  (Δ c.pre.memReads ∪ (c.pre.intraInstructionOrder ; c.regReadsFromData)⁺) ;
  c.pre.intraInstructionOrder ;
  Δ c.pre.memWriteReqs

def atomicUpdate (c : Cand nThreads) : Rel Eid :=
  c.pre.sameInstructionInstance ∩
  (setProd (c.pre.memReads) (c.pre.memWrites)) ∩
  c.pre.sameFootprint

end Cand

inductive AxiomaticModel.Behavior (Flag : Type) where
  | allowed
  | rejected
  | flagged (f : Flag)
deriving Repr

def AxiomaticModel [Arch] [ArchExtra] (Flag : Type)
  := (nThreads : Nat) → Cand nThreads
  → Except String (AxiomaticModel.Behavior Flag)

end ArchSem.CandidateExecutions

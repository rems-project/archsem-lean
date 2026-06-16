-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.ListSet

/-!
This file provies monad types to help with non-deterministic state transitions
used in various concurrency models.
-/

namespace ArchSem.NondeterministicMonad

/--
Non-deterministic Except.
Finite non-determinisim only.
In a non-deterministic transition system consisting of nodes from `α`
and error states from `ε`, `oks` and `errors` represents the set of
current ok states and error states respectivly.

A common usecase is to specialize with `NExcept (σ × ε) (σ × α)` where
`σ` represents a model state, and `α` a return value.
We have some helper functions for working on a `NExcept` of this form.
-/
@[ext]
structure NExcept (ε α : Type) where
  oks : ListSet α
  errors : ListSet ε

namespace NExcept

/-- Return true iff any error states are present. -/
def hasError (e : NExcept ε α) : Bool :=
  not e.errors.isEmpty

/-- Take the union of two state sets. -/
def merge (m1 m2 : NExcept ε α) : NExcept ε α :=
  { oks := m1.oks.union m2.oks, errors := m1.errors.union m2.errors }

/-- Nondeterministically choose an element from a ListSet. -/
def choose (s : ListSet α) : NExcept ε α :=
  { oks := s, errors := ListSet.ofList [] }

/-- The non-deterministic empty state. -/
def empty : NExcept ε α :=
  { oks := ListSet.empty, errors := ListSet.empty }

/-- Non-deterministically choose a `Fin n`. -/
def chooseFin (n : Nat) : NExcept ε (Fin n) :=
  choose (ListSet.ofList (List.finRange n))

/-- Non-deterministic state containing only the error `e`. -/
def error (e : ε) : NExcept ε α :=
  { oks := ListSet.ofList [], errors := ListSet.ofList [e] }

def map (f : α → β) (m : NExcept ε α) : NExcept ε β :=
  { oks := ListSet.map f m.oks, errors := m.errors }
def pure (v : α) : NExcept ε α :=
  { oks := ListSet.ofList [v], errors := ListSet.ofList [] }
def bind (m : NExcept ε α) (f : α → NExcept ε β) : NExcept ε β :=
  let successors := m.oks.map f
  { oks := (successors.map NExcept.oks).flatten
  , errors := m.errors.union (successors.map NExcept.errors).flatten}

instance : Functor (NExcept ε) where
  map := map

instance : Monad (NExcept ε) where
  pure := pure
  bind := bind

/-- Lift a deterministic state into a non-deterministic. -/
instance : MonadLift (Except ε) (NExcept ε) where
  monadLift r := match r with
    | .ok a => { oks := ListSet.ofList [a], errors := ListSet.ofList [] }
    | .error e => { oks := ListSet.ofList [], errors := ListSet.ofList [e] }

/-- Map only the state of a `NExcept (σ × ε) (σ × α)`. -/
def mapState (f : σ → σ') (r : NExcept (σ × ε) (σ × α)) : NExcept (σ' × ε) (σ' × α) :=
  { oks := r.oks.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }

theorem bind_iff {ε α β} (b : β) (m : NExcept ε α) (f : α → NExcept ε β)
     : b ∈ (NExcept.bind m f).oks ↔ ∃ (a : α), a ∈ m.oks ∧ b ∈ (f a).oks
  := by
  simp only [NExcept.bind, ListSet.mem_flatten, ListSet.mem_map]
  apply Iff.intro
  · rintro ⟨_, ⟨⟨t, ⟨a, ha, heq⟩, _, _⟩, hmem⟩⟩
    refine ⟨a, ha, ?_⟩
    simp [heq, hmem]
  · rintro ⟨a, ha, hf⟩
    refine ⟨(f a).oks, ⟨f a, ⟨a, ha, rfl⟩, rfl⟩, hf⟩

end NExcept


/--
Non-deterministic error state monad (`Exec` in archsem-rocq).
i.e. a non-deterministic version of `EStateM`.
Finite non-determinisim only.
-/
def NEStateM (ε σ α : Type) : Type := σ → NExcept (σ × ε) (σ × α)

namespace NEStateM

/-- Non-deterministically choose an element from the ListSet, ignoring state. -/
def choose (res : ListSet α) : NEStateM σ ε α :=
  fun s => NExcept.choose (res.map (fun r => (s, r)))

/-- Non-deterministically choose a `Fin n`, ignoring state. -/
def chooseFin (n : Nat) : NEStateM σ ε (Fin n) :=
  choose (ListSet.ofList (List.finRange n))

/-- Non-determistically throw all errors in the ListSet, ignoring state. -/
def throwErrors (errors : ListSet ε) : NEStateM ε σ α :=
  fun s => { oks := ListSet.empty, errors := errors.map (fun e => (s, e))}

/-- Non-deterministically throw a single error, ignoring state. -/
def error (err : ε) : NEStateM ε σ α := throwErrors (ListSet.ofList [err])

def mapError (f : ε → ε') (m : NEStateM ε σ α) : NEStateM ε' σ α :=
  fun s =>
    let res := m s
    { oks := res.oks
    , errors := res.errors.map (fun (s', a) => (s', f a)) }

def map (f : α → β) (m : NEStateM ε σ α) : NEStateM ε σ β :=
  fun s => NExcept.map (fun (s, a) => (s, f a)) (m s)
def pure (a : α) : NEStateM ε σ α :=
  fun s => NExcept.pure (s, a)
def bind (m : NEStateM ε σ α) (f : α → NEStateM ε σ β) : NEStateM ε σ β
  := fun s => do
    let (s', a) ← m s
    f a s'
def get : NEStateM ε σ σ := fun s => .pure (s, s)

instance : Functor (NEStateM σ ε) where
  map := map

instance : Monad (NEStateM ε σ) where
  pure := pure
  bind := bind

instance : MonadState σ (NEStateM ε σ) where
  get := get
  set s _ := .pure (s, ())
  modifyGet f s :=
    let (a, s') := f s
    .pure (s', a)

instance : MonadLift (NExcept ε) (NEStateM ε σ) where
  monadLift r := fun s =>
    { oks := r.oks.map (fun a => (s, a))
    , errors := r.errors.map (fun e => (s, e)) }

/-- Lift the monad into another state space using arbitrary getter and setter. -/
def liftStateFull (getter : σ → σ') (setter : σ' → σ → σ)
    (inner : NEStateM ε σ' α) : NEStateM ε σ α :=
  fun s => NExcept.mapState (fun s' => setter s' s) (inner (getter s))

/-- Transition to the non-deterministic empty state. -/
def discard : NEStateM ε σ α :=
  fun _ => NExcept.empty

/--
Return a pure value, ignoring state, if the option is some.
discard all non-deterministic states if the option is none.
-/
def discardNone : Option α → NEStateM σ ε α
  | some a => pure a
  | none => discard

theorem ext {m₁ m₂ : NEStateM ε σ α} (h : ∀ s, m₁ s = m₂ s) : m₁ = m₂ := by
  exact funext h

theorem bind_iff {ε σ α β} (s₀ : σ) (s : σ) (b : β) (m : NEStateM ε σ α) (f : α → NEStateM ε σ β)
    : (s, b) ∈ (Bind.bind m f s₀).oks ↔ ∃ (s' : σ) (a : α), (s', a) ∈ (m s₀).oks ∧ (s, b) ∈ (f a s').oks
  := by
  have h_base := @NExcept.bind_iff (σ × ε) (σ × α) (σ × β) (s, b) (m s₀) (fun p => f p.snd p.fst)
  simp [Bind.bind, NEStateM.bind, h_base]

theorem bind_mono {m₁ m₂ : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m₁ s).oks, sa ∈ (m₂ s).oks)
    → (∀ sa ∈ (m₁ s).oks, sb ∈ (f₁ sa.snd sa.fst).oks → sb ∈ (f₂ sa.snd sa.fst).oks)
    → (sb ∈ (Bind.bind m₁ f₁ s).oks → sb ∈ (Bind.bind m₂ f₂ s).oks)
  := by
  intro h_m h_f h
  rw [NEStateM.bind_iff] at h ⊢
  obtain ⟨s, a, h_sa, h⟩ := h
  refine ⟨s, a, h_m (s, a) h_sa, h_f (s, a) h_sa h⟩

theorem bind_mono_right {m : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m s).oks, sb ∈ (f₁ sa.snd sa.fst).oks → sb ∈ (f₂ sa.snd sa.fst).oks)
    → (sb ∈ (Bind.bind m f₁ s).oks → sb ∈ (Bind.bind m f₂ s).oks)
  := by
  intro h_f
  exact NEStateM.bind_mono (by simp) h_f

theorem bind_mono_left {m₁ m₂ : NEStateM ε σ α} {f : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m₁ s).oks, sa ∈ (m₂ s).oks)
    → (sb ∈ (Bind.bind m₁ f s).oks → sb ∈ (Bind.bind m₂ f s).oks)
  := by
  intro h_m
  exact NEStateM.bind_mono h_m (by simp)

theorem bind_get_elim {f : σ → NEStateM ε σ β} {s : σ}
    : Bind.bind get f s = f s s
  := by
  ext
  all_goals
    simp only [Bind.bind, NEStateM.bind, NExcept.pure, NExcept.bind, get]
    apply ListSet.ext
    simp [ListSet.mem_flatten, ListSet.mem_map, ListSet.mem_of_list, ListSet.mem_union]

theorem bind_modify_elim {f : Unit → NEStateM ε σ β} {h : σ → σ} {s : σ}
    : Bind.bind (modify h) f s = f () (h s)
  := by
  ext
  all_goals
    simp only [Bind.bind, NEStateM.bind, NExcept.pure, NExcept.bind, modify, modifyGet]
    apply ListSet.ext
    simp [ListSet.mem_flatten, ListSet.mem_map, ListSet.mem_of_list, ListSet.mem_union]

theorem bind_congr {m₁ m₂ : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β}
    : m₁ = m₂ → f₁ = f₂ → Bind.bind m₁ f₁ = Bind.bind m₂ f₂
  := by
  intro h_m h_f
  rw [h_m, h_f]

theorem bind_app_congr {m₁ m₂ : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s₁ s₂ : σ}
    : (m₁ s₁ = m₂ s₂)
    → (∀ s' ∈ (m₁ s₁).oks, f₁ s'.snd s'.fst = f₂ s'.snd s'.fst)
    → Bind.bind m₁ f₁ s₁ = Bind.bind m₂ f₂ s₂
  := by
  intro h_ms h_f
  ext
  all_goals
    simp only [Bind.bind, NEStateM.bind, NExcept.bind]
    simp only [h_ms] at ⊢ h_f
    apply congrArg
    apply congrArg
    try apply congrArg
    apply ListSet.map_congr_left
    exact h_f

theorem bind_oks_congr {m₁ m₂ : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s₁ s₂}
    : m₁ = m₂ → f₁ = f₂ → s₁ = s₂ → (Bind.bind m₁ f₁ s₁).oks = (Bind.bind m₂ f₂ s₂).oks
  := by
  intro h_m h_f h_s
  rw [h_m, h_f, h_s]

end NEStateM

end ArchSem.NondeterministicMonad

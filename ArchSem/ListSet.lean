import Std.Data.ExtTreeSet

/-!
This file implements a finite set type (similar to MathLib's FinSet) as a
Quotient type over lists. This is primarily used for representing the set of
states & results in the non-deterministic monad. Using a ListSet for this role
means that we can effectivly choose when deduplication happens: if we were
using a hash set for example, then we would be forced to hash every state after
every monadic bind which could be costly.

De-duplication is done with the `prune` function.
TODO: implement an optimized deduplication of elements using a user-supplied
      hash function.
-/

namespace ArchSem

/-- The quotient relation for ListSets: lists that contain the same elements. -/
def ListSet.r {α : Type} (a b : List α) : Prop :=
  ∀ x : α, x ∈ a ↔ x ∈ b

def ListSetSetoid (α : Type) : Setoid (List α) where
  r := ListSet.r
  iseqv := {
    refl := by
      simp [ListSet.r]
    symm := by
      simp only [ListSet.r]
      intro l₁ l₂ h
      simp [h]
    trans := by
      simp only [ListSet.r]
      intro l₁ l₂ l₃ h₁ h₂ x
      exact Iff.trans (h₁ x) (h₂ x)
  }

/--
A finite set type implemented as a list up to the elements it contains.
-/
def ListSet (α : Type) := Quotient (ListSetSetoid α)

def ListSet.empty : ListSet α := Quotient.mk (ListSetSetoid α) []

def ListSet.ofList (l : List α) : ListSet α := Quotient.mk (ListSetSetoid α) l

instance [DecidableEq α] : DecidableEq (ListSet α) := by
  intro a b
  refine Quotient.recOnSubsingleton₂ a b ?_
  intro la lb
  let p : Prop := la ⊆ lb ∧ lb ⊆ la
  have hp : p ↔ ListSet.r la lb := by
    constructor
    · intro h x
      constructor
      · intro hx
        exact h.1 hx
      · intro hx
        exact h.2 hx
    · intro h
      constructor
      · intro x hx
        exact (h x).mp hx
      · intro x hx
        exact (h x).mpr hx
  by_cases h : p
  · exact isTrue (Quotient.sound (hp.mp h))
  · exact isFalse (fun heq => h (hp.mpr (Quotient.exact heq)))

/--
Deduplicate the internal elements of the ListSet.
This has no logically observable effect (as proven by ListSet.prune_eq),
but it can improve performance depending on your usecase.
-/
def ListSet.prune (l : ListSet α) [DecidableEq α] : ListSet α :=
  Quotient.lift (fun l => ListSet.ofList l.eraseDups) (by
    intro a b h
    apply Quotient.sound
    intro x
    simpa [List.mem_eraseDups] using h x) l

/--
Prove that internal-deduplication has no observable effect.
-/
theorem ListSet.prune_eq {l : ListSet α} [DecidableEq α] : l.prune = l :=
  Quotient.inductionOn l (by
    intro l
    apply Quotient.sound
    intro x
    simp [List.mem_eraseDups])

/-- Set membership. -/
def ListSet.mem (x : α) : ListSet α → Prop :=
  Quotient.lift (fun l => x ∈ l) (by
    intro a b h
    exact propext (h x))

instance : Membership α (ListSet α) where
  mem s x := ListSet.mem x s

-- Many of the ListSet lemmas have direct analogous in List.

@[simp]
theorem ListSet.mem_of_list {x : α} {l : List α}
    : x ∈ ListSet.ofList l ↔ x ∈ l := by
  change x ∈ l ↔ x ∈ l
  simp

theorem ListSet.not_mem_empty (x : α) : x ∉ ListSet.empty := by
  change x ∉ ([] : List α)
  simp

theorem ListSet.ext {a b : ListSet α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := by
  refine Quotient.inductionOn₂ a b ?_ h
  intro la lb h
  apply Quotient.sound
  intro x
  exact h x

def ListSet.isEmpty : ListSet α → Bool :=
  Quotient.lift List.isEmpty (by
    intro a b
    intro h
    change ListSet.r a b at h
    rw [ListSet.r] at h
    cases a with
    | nil =>
      simp only [List.not_mem_nil, false_iff] at h
      simp [List.eq_nil_iff_forall_not_mem.mpr h]
    | cons head _ =>
      specialize h head
      simp only [List.mem_cons, true_or, true_iff] at h
      simp [List.ne_nil_of_mem h]
  )

def ListSet.any (p : α → Bool) : ListSet α → Bool :=
  Quotient.lift (fun a => a.any p) (by
    intro a b h
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, (h x).mp hx, hp⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨x, (h x).mpr hx, hp⟩)

theorem ListSet.any_eq_true {p : α → Bool} {s : ListSet α} :
    s.any p = true ↔ ∃ x, x ∈ s ∧ p x = true := by
  refine Quotient.inductionOn s ?_
  intro l
  change l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true
  simp only [List.any_eq_true]

theorem ListSet.any_eq_false {p : α → Bool} {s : ListSet α} :
    s.any p = false ↔ ∀ x, x ∈ s → p x = false := by
  refine Quotient.inductionOn s ?_
  intro l
  change l.any p = false ↔ ∀ x, x ∈ l → p x = false
  rw [List.any_eq_false]
  constructor
  · intro h x hx
    specialize h x hx
    cases hp : p x <;> simp [hp] at h ⊢
  · intro h x hx
    rw [h x hx]
    simp

/--
Take the union of two list sets. Internally implemented as a list append
with no-deduplication.
-/
def ListSet.union : ListSet α → ListSet α → ListSet α :=
  Quotient.lift₂ (fun a b => ListSet.ofList (a ++ b)) (by
    intro a₁ a₂ b₁ b₂ ha hb
    apply Quotient.sound
    intro x
    simp only [List.mem_append]
    constructor
    · rintro (h | h)
      · exact Or.inl ((ha x).mp h)
      · exact Or.inr ((hb x).mp h)
    · rintro (h | h)
      · exact Or.inl ((ha x).mpr h)
      · exact Or.inr ((hb x).mpr h))

/--
Map set elements. Internally implemented as a List map with no deduplication.
-/
def ListSet.map (f : α → β) : ListSet α → ListSet β :=
  Quotient.lift (fun a => ListSet.ofList (a.map f)) (by
    intro a b h
    apply Quotient.sound
    intro y
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (h x).mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (h x).mpr hx, rfl⟩)

/--
Filter map set elements. Internally implemented as a List filtermap with no
deduplication.
-/
def ListSet.filterMap (f : α → Option β) : ListSet α → ListSet β :=
  Quotient.lift (fun a => ListSet.ofList (a.filterMap f)) (by
    intro a b h
    apply Quotient.sound
    intro y
    simp only [List.mem_filterMap]
    constructor
    · rintro ⟨x, hx, hf⟩
      exact ⟨x, (h x).mp hx, hf⟩
    · rintro ⟨x, hx, hf⟩
      exact ⟨x, (h x).mpr hx, hf⟩)

theorem ListSet.map_congr_left {l : ListSet α} {f g : α → β} (h : ∀ x ∈ l, f x = g x)
    : ListSet.map f l = ListSet.map g l := by
  revert h
  refine Quotient.inductionOn l ?_
  intro ls h
  apply ListSet.ext
  intro x
  change x ∈ ls.map f ↔ x ∈ ls.map g
  change ∀ x, x ∈ ls → f x = g x at h
  simp only [List.mem_map]
  apply Iff.intro
  · rintro ⟨a, ha, hf⟩
    refine ⟨a, ha, ?_⟩
    rw [← h a ha]
    exact hf
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    rw [h a ha]
    exact hg

theorem ListSet.mem_map {x : β} {a : ListSet α} {f : α → β} :
    x ∈ a.map f ↔ ∃ y, y ∈ a ∧ f y = x := by
  simp only [ListSet.map]
  refine Quotient.inductionOn a ?_
  intro a
  change x ∈ List.map f a ↔ ∃ y, y ∈ a ∧ f y = x
  simp [List.mem_map]

theorem ListSet.mem_union (x : α) (a b : ListSet α) :
    x ∈ ListSet.union a b ↔ x ∈ a ∨ x ∈ b := by
  refine Quotient.inductionOn₂ a b ?_
  intro la lb
  change ListSet.mem x (ListSet.ofList (la ++ lb)) ↔
    ListSet.mem x (ListSet.ofList la) ∨ ListSet.mem x (ListSet.ofList lb)
  simp [ListSet.mem, ListSet.ofList, Quotient.lift, Quotient.mk, List.mem_append]

theorem ListSet.mem_foldr_union (x : α) (sets : List (ListSet α)) :
    x ∈ sets.foldr ListSet.union (ListSet.ofList []) ↔ ∃ s, s ∈ sets ∧ x ∈ s := by
  induction sets with
  | nil =>
    change ListSet.mem x (ListSet.ofList ([] : List α)) ↔ ∃ s, s ∈ [] ∧ x ∈ s
    simp [ListSet.mem, ListSet.ofList, Quotient.lift, Quotient.mk]
  | cons s sets ih =>
    simp [List.foldr, ListSet.mem_union, ih, or_and_right, exists_or]

/--
Flatten the elements of a nested ListSet. This does no internal deduplication
so consider running ListSet.prune afterwards.
-/
def ListSet.flatten : ListSet (ListSet α) → ListSet α :=
  Quotient.lift (fun sets => sets.foldr ListSet.union ListSet.empty) (by
    intro a b h
    apply ListSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := (ListSet.mem_foldr_union x a).mp hx
      exact (ListSet.mem_foldr_union x b).mpr ⟨s, (h s).mp hs, hxs⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := (ListSet.mem_foldr_union x b).mp hx
      exact (ListSet.mem_foldr_union x a).mpr ⟨s, (h s).mpr hs, hxs⟩)

def ListSet.mem_flatten (x : α) (a : ListSet (ListSet α)) :
    x ∈ a.flatten ↔ ∃ b, b ∈ a ∧ x ∈ b := by
  refine Quotient.inductionOn a ?_
  intro as
  induction as with
  | nil =>
    simp only [flatten]
    change x ∈ [] ↔ ∃ b, b ∈ [] ∧ x ∈ b
    simp
  | cons h t ih =>
    simp only [flatten] at ⊢ ih
    change x ∈ List.foldr union empty (h::t) ↔ ∃ b, b ∈ (h::t) ∧ x ∈ b
    change x ∈ List.foldr union empty t ↔ ∃ b, b ∈ t ∧ x ∈ b at ih
    simp [ListSet.mem_union, ih]

/--
Extract the elements of a ListSet to a deduplicated and sorted list.
We must specify a normalized order so that all equal ListSet's output
the same list from this function.
-/
def ListSet.toSortedList (cmp : α → α → Ordering) [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] [DecidableEq α] : ListSet α → List α :=
  Quotient.lift (Std.ExtTreeSet.ofList · cmp |>.toList) (by
    intro l₁ l₂ hq
    simp only []
    congr 1
    rw [Std.ExtTreeSet.ext_mem_iff]
    intro x
    simpa [Std.ExtTreeSet.mem_ofList, List.contains_eq_mem] using hq x
  )

end ArchSem

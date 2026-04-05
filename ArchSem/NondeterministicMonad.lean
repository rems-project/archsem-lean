/-!
This file provies monad types to help with non-deterministic state transitions
used in various concurrency models.
This file is an analogous of archsem-rocq's `Common/Exec.v`.
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

The order of the lists does not matter (TODO: implement equality instances).
-/
structure NExcept (ε α : Type) where
  oks : List α
  errors : List ε

namespace NExcept

/-- Return true iff any error states are present. -/
def hasError (e : NExcept ε α) : Bool :=
  match e.errors with
  | [] => false
  | _ => true

/-- Take the union of two state sets. -/
def merge (m1 m2 : NExcept ε α) : NExcept ε α :=
  { oks := m1.oks ++ m2.oks, errors := m1.errors ++ m2.errors }

/-- Nondeterministically choose an element from a list. -/
def choose (s : List α) : NExcept ε α :=
  { oks := s, errors := [] }

/-- The non-deterministic empty state. -/
def empty : NExcept ε α :=
  { oks := [], errors := [] }

/-- Non-deterministically choose a `Fin n`. -/
def chooseFin (n : Nat) : NExcept ε (Fin n) := choose (List.finRange n)

/-- Non-deterministic state containing only the error `e`. -/
def error (e : ε) : NExcept ε α := { oks := [], errors := [e] }

def map (f : α → β) (m : NExcept ε α) : NExcept ε β :=
  { oks := List.map f m.oks, errors := m.errors }
def pure (v : α) : NExcept ε α :=
  { oks := [v], errors := [] }
def bind (m : NExcept ε α) (f : α → NExcept ε β) :=
  (m.oks.map f).foldr NExcept.merge { oks := [], errors := m.errors }

instance : Functor (NExcept ε) where
  map := map

instance : Monad (NExcept ε) where
  pure := pure
  bind := bind

/-- Lift a deterministic state into a non-deterministic. -/
instance : MonadLift (Except ε) (NExcept ε) where
  monadLift r := match r with
    | .ok a => { oks := [a], errors := [] }
    | .error e => { oks := [], errors := [e] }

/-- Return all states in a list. Arbitrary order. -/
def toExceptList (m : NExcept ε α) : List (Except ε α) :=
  (m.oks.map Except.ok) ++ (m.errors.map Except.error)

/-- Return all states paired with values in a list. -/
def toStatefulExceptList (m : NExcept (σ × ε) (σ × α)) : List (σ × Except ε α) :=
  List.append
    (m.oks.map (fun (s, r) => (s, Except.ok r)))
    (m.errors.map (fun (s, err) => (s, Except.error err)))

/-- Map only the state of a `NExcept (σ × ε) (σ × α)`. -/
def mapState (f : σ → σ') (r : NExcept (σ × ε) (σ × α)) : NExcept (σ' × ε) (σ' × α) :=
  { oks := r.oks.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }

end NExcept


/--
Non-deterministic error state monad (`Exec` in archsem-rocq).
i.e. a non-deterministic version of `EStateM`.
Finite non-determinisim only.
-/
def NEStateM (ε σ α : Type) : Type := σ → NExcept (σ × ε) (σ × α)

namespace NEStateM

/-- Non-deterministically choose an element from the list, ignoring state. -/
def choose (res : List α) : NEStateM σ ε α :=
  fun s => NExcept.choose (res.map (fun r => (s, r)))

/-- Non-deterministically choose a `Fin n`, ignoring state. -/
def chooseFin (n : Nat) : NEStateM σ ε (Fin n) :=
  choose (List.finRange n)

/-- Non-determistically throw all errors in the list, ignoring state. -/
def throwErrors (errors : List ε) : NEStateM ε σ α :=
  fun s => { oks := [], errors := errors.map (fun e => (s, e))}

/-- Non-deterministically throw a single error, ignoring state. -/
def error (err : ε) : NEStateM ε σ α := throwErrors [err]

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

instance : Functor (NEStateM σ ε) where
  map := map

instance : Monad (NEStateM ε σ) where
  pure := pure
  bind := bind

instance : MonadState σ (NEStateM ε σ) where
  get s := .pure (s, s)
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

end NEStateM

section Lemmas

theorem NExcept.bind_iff {ε α β} (b : β) (m : NExcept ε α) (f : α → NExcept ε β)
     : b ∈ (NExcept.bind m f).oks ↔ ∃ (a : α), a ∈ m.oks ∧ b ∈ (f a).oks
  := by
  simp only [NExcept.bind]
  induction m.oks with
  | nil =>
    apply Iff.intro
    all_goals simp
  | cons a tail ih =>
    simp only [NExcept.merge, List.foldr, List.map, List.mem_append]
    apply Iff.intro
    case mp =>
      rintro (h | h)
      · simp [h]
      · simp [ih.mp h]
    case mpr =>
      rintro ⟨a, h_in, h_in_ok⟩
      cases h_in with
      | head => exact Or.inl h_in_ok
      | tail _ h_in_tail => exact Or.inr (ih.mpr ⟨a, h_in_tail, h_in_ok⟩)

theorem NEStateM.bind_iff {ε σ α β} (s₀ : σ) (s : σ) (b : β) (m : NEStateM ε σ α) (f : α → NEStateM ε σ β)
    : (s, b) ∈ (NEStateM.bind m f s₀).oks ↔ ∃ (s' : σ) (a : α), (s', a) ∈ (m s₀).oks ∧ (s, b) ∈ (f a s').oks
  := by
  have h_base := @NExcept.bind_iff (σ × ε) (σ × α) (σ × β) (s, b) (m s₀) (fun p => f p.snd p.fst)
  simp [Bind.bind, NEStateM.bind, h_base]

end Lemmas

end ArchSem.NondeterministicMonad

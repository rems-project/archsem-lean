/-
This file provies monad types to help with non-deterministic state transitions
used in various concurrency models.
This file is an analogous of archsem-rocq's `Common/Exec.v`.
-/

namespace ArchSem.NondeterministicMonad

/- Non-deterministic Except type can have multiple ok states and multiple errors. -/
structure NExcept (ε α : Type) where
  oks : List α
  errors : List ε

namespace NExcept

def hasError (e : NExcept ε α) : Bool :=
  match e.errors with
  | [] => false
  | _ => true

def merge (m1 m2 : NExcept ε α) : NExcept ε α :=
  { oks := m1.oks ++ m2.oks, errors := m1.errors ++ m2.errors }
def choose (s : List α) : NExcept ε α :=
  { oks := s, errors := [] }
def error (e : ε) : NExcept ε α := { oks := [], errors := [e] }

def chooseFin (n : Nat) : NExcept ε (Fin n) := choose (List.finRange n)

def toExceptList (m : NExcept ε α) : List (Except ε α) :=
  (m.oks.map Except.ok) ++ (m.errors.map Except.error)

instance : Functor (NExcept ε) where
  map f m := { oks := List.map f m.oks, errors := m.errors }

instance : Monad (NExcept ε) where
  pure v := { oks := [v], errors := [] }
  bind m f := (m.oks.map f).foldr NExcept.merge { oks := [], errors := m.errors }

instance : MonadLift (Except ε) (NExcept ε) where
  monadLift r := match r with
    | .ok a => { oks := [a], errors := [] }
    | .error e => { oks := [], errors := [e] }

def toStatefulExceptList (m : NExcept (σ × ε) (σ × α)) : List (σ × Except ε α) :=
  List.append
    (m.oks.map (fun (s, r) => (s, Except.ok r)))
    (m.errors.map (fun (s, err) => (s, Except.error err)))
def toStateExceptList (m : NExcept (σ × ε) (σ × α)) : List (Except σ σ) :=
  List.append
    (m.oks.map (fun (s, _r) => Except.ok s))
    (m.errors.map (fun (s, _err) => Except.error s))
def successStateList (m : NExcept (σ × ε) (σ × α)) : List σ :=
  m.oks.map (fun (s, _r) => s)
def mapState (f : σ → σ') (r : NExcept (σ × ε) (σ × α)) : NExcept (σ' × ε) (σ' × α) :=
  { oks := r.oks.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }

end NExcept


/- Non-deterministic Error State Monad (`Exec` in archsem-rocq). Finite non-determinisim only. -/
def NEStateM (ε σ α : Type) : Type := σ → NExcept (σ × ε) (σ × α)

namespace NEStateM

def choose (res : List α) : NEStateM σ ε α :=
  fun s => NExcept.choose (res.map (fun r => (s, r)))
def throwErrors (errors : List ε) : NEStateM ε σ α :=
  fun s => { oks := [], errors := errors.map (fun e => (s, e))}
def discard : NEStateM σ ε α :=
  fun _ => { oks := [], errors := [] }

instance : Functor (NEStateM σ ε) where
  map f e := fun s =>  Functor.map (fun (s, a) => (s, f a)) (e s)

instance : Monad (NEStateM σ ε) where
  pure a := fun s => pure (s, a)
  bind m f := fun s => do
    let (s', a) ← m s
    f a s'

instance : MonadState σ (NEStateM ε σ) where
  get s := pure (s, s)
  set s _ := pure (s, ())
  modifyGet f s :=
    let (a, s') := f s
    pure (s', a)

instance : MonadLift (NExcept ε) (NEStateM ε σ) where
  monadLift r := fun s =>
    { oks := r.oks.map (fun a => (s, a))
    , errors := r.errors.map (fun e => (s, e)) }

def error (err : ε) : NEStateM ε σ α := throwErrors [err]
def chooseFin (n : Nat) : NEStateM σ ε (Fin n) := choose (List.finRange n)

def discardNone : Option α → NEStateM σ ε α
  | some a => pure a
  | none => discard

def liftStateFull (getter : σ → σ') (setter : σ' → σ → σ)
    (inner : NEStateM ε σ' α) : NEStateM ε σ α :=
  fun s => NExcept.mapState (fun s' => setter s' s) (inner (getter s))

def mapError (f : ε → ε') (m : NEStateM ε σ α) : NEStateM ε' σ α :=
  fun s =>
    let res := m s
    { oks := res.oks
    , errors := res.errors.map (fun (s', e) => (s', f e)) }

end NEStateM

end ArchSem.NondeterministicMonad

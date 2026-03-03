/- Conversion of archsem/Common/NEStateM.v -/

namespace ExecutionMonad

/- CR clang: I should comment this code making references to the paper. https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf -/

/-
 - CR clang: There is some naming inconsistency here. In lean we call
 - Result `Except`. So maybe `NExcept` is better?
 - Should we be using the archsem Result type?
 -/

/- Non-deterministic Result. (`Res` in archsem-rocq) -/
structure NResult (ε α : Type) where
  results : List α
  errors : List ε

namespace NResult

def hasError (e : NResult ε α) : Bool :=
  match e.errors with
  | [] => false
  | _ => true

def merge (m1 m2 : NResult ε α) : NResult ε α :=
  { results := m1.results ++ m2.results, errors := m1.errors ++ m2.errors }
def fromResults (s : List α) : NResult ε α :=
  { results := s, errors := [] }
def error (e : ε) : NResult ε α := { results := [], errors := [e] }

def chooseFin (n : Nat) : NResult ε (Fin n) := { results := List.finRange n, errors := []}

/- CR clang: Maybe to `Except` list? -/
def toResultList (m : NResult ε α) : List (Except ε α) :=
  (m.results.map Except.ok) ++ (m.errors.map Except.error)

instance : Functor (NResult ε) where
  map f m := { results := List.map f m.results, errors := m.errors }

instance : Monad (NResult ε) where
  pure v := { results := [v], errors := [] }
  bind m f := (m.results.map f).foldr NResult.merge { results := [], errors := m.errors }

instance : MonadLift (Except ε) (NResult ε) where
  monadLift r := match r with
    | .ok a => { results := [a], errors := [] }
    | .error e => { results := [], errors := [e] }

def toStatefulResultList (m : NResult (σ × ε) (σ × α)) : List (σ × Except ε α) :=
  List.append
    (m.results.map (fun (s, r) => (s, Except.ok r)))
    (m.errors.map (fun (s, err) => (s, Except.error err)))
def toStateResultList (m : NResult (σ × ε) (σ × α)) : List (Except σ σ) :=
  List.append
    (m.results.map (fun (s, _r) => Except.ok s))
    (m.errors.map (fun (s, _err) => Except.error s))
def successStateList (m : NResult (σ × ε) (σ × α)) : List σ :=
  m.results.map (fun (s, _r) => s)
def mapState (f : σ → σ') (r : NResult (σ × ε) (σ × α)) : NResult (σ' × ε) (σ' × α) :=
  { results := r.results.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }

end NResult


/- Non-deterministic Error State Monad (`Exec` in archsem-rocq). -/
def NEStateM (σ ε α : Type) : Type := σ → NResult (σ × ε) (σ × α)

namespace NEStateM

def results (res : List α) : NEStateM σ ε α :=
  fun s => NResult.fromResults (res.map (fun r => (s, r)))
def errors (errors : List ε) : NEStateM σ ε α :=
  fun s => { results := [], errors := errors.map (fun e => (s, e))}
def discard : NEStateM σ ε α :=
  fun _ => { results := [], errors := [] }

instance : Functor (NEStateM σ ε) where
  map f e := fun st => (fun (st, a) => (st, f a)) <$> (e st)

instance : Monad (NEStateM σ ε) where
  pure a := fun s => pure (s, a)
  bind m f := fun s => do
    let (s', a) ← m s
    f a s'

instance : MonadState σ (NEStateM σ ε) where
  get s := pure (s, s)
  set s _ := pure (s, ())
  modifyGet f s :=
    let (a, s') := f s
    pure (s', a)

instance : MonadLift (NResult ε) (NEStateM σ ε) where
  monadLift r := fun s =>
    { results := r.results.map (fun a => (s, a))
    , errors := r.errors.map (fun e => (s, e)) }

def error (err : ε) : NEStateM σ ε α := errors [err]
def chooseFin (n : Nat) : NEStateM σ ε (Fin n) := results (List.finRange n)

def discardNone : Option α → NEStateM σ ε α
  | some a => pure a
  | none => discard

/- CR clang: Maybe rename liftState{,Full} functions? -/
/- CR clang for leo: Lets talk about this: -/
def liftState (getter : σ → σ') (inner : NEStateM σ' ε α) : NEStateM σ ε α
  := sorry
def liftStateFull (getter : σ → σ') (setter : σ' → σ → σ)
    (inner : NEStateM σ' ε α) : NEStateM σ ε α :=
  fun s => NResult.mapState (fun s' => setter s' s) (inner (getter s))

def mapError (f : ε → ε') (m : NEStateM σ ε α) : NEStateM σ ε' α :=
  fun s =>
    let res := m s
    { results := res.results
    , errors := res.errors.map (fun (s', e) => (s', f e)) }

end NEStateM

end ExecutionMonad

-- Conversion of archsem/Common/Exec.v

namespace ExecutionMonad

/- CR clang: I should comment this code making references to the paper. https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf -/
/- CR clang for thibaut:
    I'd like to rename `Res` and `Exec`.
    `Res` -> `NResult` (non-deterministic result)
    `Exec` -> `NEStateM` (non-deterministic error state monad)
    clang: Lets do thie but leave comment linking back to what the archsem rocq names are.
-/

/- Base execution result definitions -/
structure Res (ε α : Type) where
  results : List α
  errors : List ε

def Res.hasError (e : Res ε α) : Bool :=
  match e.errors with
  | [] => false
  | _ => true

def Res.merge (m1 m2 : Res ε α) : Res ε α :=
  { results := m1.results ++ m2.results, errors := m1.errors ++ m2.errors }
def Res.fromResults (s : List α) : Res ε α :=
  { results := s, errors := [] }
def Res.error (e : ε) : Res ε α := { results := [], errors := [e] }

/-
instance : Functor (Res ε) where
  map f m := { results := List.map f m.results, errors := m.errors }
-/

instance : Monad (Res ε) where
  pure v := { results := [v], errors := [] }
  bind m f := (m.results.map f).foldr Res.merge { results := [], errors := m.errors }
/-
instance : MonadExcept ε (Res ε) where
  throw e := { results := [], errors := [e] }
  tryCatch := ...
-/
instance : MonadLift (Except ε) (Res ε) where
  monadLift r := match r with
    | .ok a => { results := [a], errors := [] }
    | .error e => { results := [], errors := [e] }
  
/-
class MonadChoose (m : Type → Type) where
  choose {A : Type} (l : List A) : m A
def chooseFin {m} [MonadChoose m] (n : Nat) : m (Fin n) :=
  MonadChoose.choose (List.finRange n)
instance {E} : MonadChoose (Res E) where
  choose l := { results := l, errors := [] }
-/

def Res.chooseFin (n : Nat) : Res ε (Fin n) := { results := List.finRange n, errors := []}

/- CR clang: should I use the archsem result type instead of Except? -/
def Res.toResultList (m : Res ε α) : List (Except ε α) :=
  (m.results.map Except.ok) ++ (m.errors.map Except.error)

def Res.toStatefulResultList (m : Res (σ × ε) (σ × α)) : List (σ × Except ε α) :=
  List.append
    (m.results.map (fun (s, r) => (s, Except.ok r)))
    (m.errors.map (fun (s, err) => (s, Except.error err)))
def Res.toStateResultList (m : Res (σ × ε) (σ × α)) : List (Except σ σ) :=
  List.append
    (m.results.map (fun (s, _r) => Except.ok s))
    (m.errors.map (fun (s, _err) => Except.error s))
def Res.successStateList (m : Res (σ × ε) (σ × α)) : List σ :=
  m.results.map (fun (s, _r) => s)

def Exec (σ ε α : Type) : Type := σ → Res (σ × ε) (σ × α)
def Exec.results (res : List α) : Exec σ ε α :=
  fun s => Res.fromResults (res.map (fun r => (s, r)))
def Exec.errors (errors : List ε) : Exec σ ε α :=
  fun s => { results := [], errors := errors.map (fun e => (s, e))}
/-
instance : Functor (Exec σ ε) where
  map f e := fun st => (fun (st, a) => (st, f a)) <$> (e st)
-/
instance : Monad (Exec σ ε) where
  pure a := fun s => pure (s, a)
  bind m f := fun s => do
    let (s', a) ← m s
    f a s'

def Exec.error (err : ε) : Exec σ ε α := fun s => { results := [], errors := [(s, err)] }

/-
instance : MonadError E (Exec St E) where
  throw e := fun st => throw (st, e)
instance : Res.MonadChoose (Exec St E) where
  choose l := fun st => Res.choose (l.map (fun a => (st, a)))
-/

def Exec.chooseFin (n : Nat) : Exec σ ε (Fin n) :=
  fun s => { results := List.ofFn (fun x : (Fin n) => (s, x)), errors := [] }

instance : MonadState σ (Exec σ ε) where
  get s := pure (s, s)
  set s _ := pure (s, ())
  modifyGet f s :=
    let (a, s') := f s
    pure (s', a)

instance : MonadLift (Res ε) (Exec σ ε) where
  monadLift r := fun s =>
    { results := r.results.map (fun a => (s, a))
    , errors := r.errors.map (fun e => (s, e)) }

def Exec.discard : Exec σ ε α := fun _ => { results := [], errors := [] }

/- CR clang: Lets do some better namespacing in this file... -/
def mapState (f : σ → σ') (r : Res (σ × ε) (σ × α)) : Res (σ' × ε) (σ' × α) :=
  { results := r.results.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }
  
/- CR clang: Maybe rename liftState{,Full} functions? -/
def Exec.liftStateFull (getter : σ → σ') (setter : σ' → σ → σ)
    (inner : Exec σ' ε α) : Exec σ ε α :=
  fun s => mapState (fun s' => setter s' s) (inner (getter s))

  /- CR clang: for now just spefify setter manually and ask leo later... -/
  /-
def Exec.liftState (getter : σ → σ') (inner : Exec σ' ε α) : Exec σ ε α :=
  /- CR clang for thibaut: So I'm not sure how to translate this
    liftSt_full getter (@setv _ _ getter _) inner.
  -/
  Exec.liftStateFull getter (fun s' s => sorry) inner
  -/

/-
def Exec.elemOfResults {E A} (x : A) (r : Res E A) : Prop :=
  x ∈ r.results
def Exec.elemOfResultsNoState {St E A} (x : A) (r : Res (St × E) (St × A)) : Prop :=
  x ∈ (r.results.map Prod.snd)
def Exec.elemOfResult {E A} (x : Except E A) (e : Res E A) : Prop :=
  match x with
  | .ok v => v ∈ e.results
  | .error err => err ∈ e.errors
def Exec.elemOfResultNoState {St E A} (x : Except E A) (e : Res (St × E) (St × A)) : Prop :=
  match x with
  | .ok v => v ∈ (e.results.map Prod.snd)
  | .error err => err ∈ (e.errors.map Prod.snd)
-/
def Exec.discardNone : Option α → Exec σ ε α
  | some a => pure a
  | none => discard
def Exec.mapError (f : ε → ε') (m : Exec σ ε α) : Exec σ ε' α :=
  fun s =>
    let res := m s
    { results := res.results, errors := res.errors.map (fun (s', e) => (s', f e)) }

end ExecutionMonad

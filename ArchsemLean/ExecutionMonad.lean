-- Conversion of archsem/Common/NEStateM.v

namespace ExecutionMonad

/- CR clang: I should comment this code making references to the paper. https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf -/

/- Base execution result definitions -/
/- Non-deterministic Result. (`Res` in archsem-rocq) -/
structure NResult (ε α : Type) where
  results : List α
  errors : List ε

def NResult.hasError (e : NResult ε α) : Bool :=
  match e.errors with
  | [] => false
  | _ => true

def NResult.merge (m1 m2 : NResult ε α) : NResult ε α :=
  { results := m1.results ++ m2.results, errors := m1.errors ++ m2.errors }
def NResult.fromResults (s : List α) : NResult ε α :=
  { results := s, errors := [] }
def NResult.error (e : ε) : NResult ε α := { results := [], errors := [e] }

/-
instance : Functor (Res ε) where
  map f m := { results := List.map f m.results, errors := m.errors }
-/

instance : Monad (NResult ε) where
  pure v := { results := [v], errors := [] }
  bind m f := (m.results.map f).foldr NResult.merge { results := [], errors := m.errors }
/-
instance : MonadExcept ε (Res ε) where
  throw e := { results := [], errors := [e] }
  tryCatch := ...
-/
instance : MonadLift (Except ε) (NResult ε) where
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

def NResult.chooseFin (n : Nat) : NResult ε (Fin n) := { results := List.finRange n, errors := []}

/- CR clang: should I use the archsem result type instead of Except? -/
def NResult.toResultList (m : NResult ε α) : List (Except ε α) :=
  (m.results.map Except.ok) ++ (m.errors.map Except.error)

def NResult.toStatefulResultList (m : NResult (σ × ε) (σ × α)) : List (σ × Except ε α) :=
  List.append
    (m.results.map (fun (s, r) => (s, Except.ok r)))
    (m.errors.map (fun (s, err) => (s, Except.error err)))
def NResult.toStateResultList (m : NResult (σ × ε) (σ × α)) : List (Except σ σ) :=
  List.append
    (m.results.map (fun (s, _r) => Except.ok s))
    (m.errors.map (fun (s, _err) => Except.error s))
def NResult.successStateList (m : NResult (σ × ε) (σ × α)) : List σ :=
  m.results.map (fun (s, _r) => s)

/- Non-deterministic Error State Monad (`Exec` in archsem-rocq). -/
def NEStateM (σ ε α : Type) : Type := σ → NResult (σ × ε) (σ × α)
def NEStateM.results (res : List α) : NEStateM σ ε α :=
  fun s => NResult.fromResults (res.map (fun r => (s, r)))
def NEStateM.errors (errors : List ε) : NEStateM σ ε α :=
  fun s => { results := [], errors := errors.map (fun e => (s, e))}
/-
instance : Functor (Exec σ ε) where
  map f e := fun st => (fun (st, a) => (st, f a)) <$> (e st)
-/
instance : Monad (NEStateM σ ε) where
  pure a := fun s => pure (s, a)
  bind m f := fun s => do
    let (s', a) ← m s
    f a s'

def NEStateM.error (err : ε) : NEStateM σ ε α := fun s => { results := [], errors := [(s, err)] }

/-
instance : MonadError E (Exec St E) where
  throw e := fun st => throw (st, e)
instance : NResult.MonadChoose (Exec St E) where
  choose l := fun st => NResult.choose (l.map (fun a => (st, a)))
-/

def NEStateM.chooseFin (n : Nat) : NEStateM σ ε (Fin n) :=
  fun s => { results := List.ofFn (fun x : (Fin n) => (s, x)), errors := [] }

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

def NEStateM.discard : NEStateM σ ε α := fun _ => { results := [], errors := [] }

/- CR clang: Lets do some better namespacing in this file... -/
def mapState (f : σ → σ') (r : NResult (σ × ε) (σ × α)) : NResult (σ' × ε) (σ' × α) :=
  { results := r.results.map (fun (s, a) => (f s, a))
  , errors := r.errors.map (fun (s, e) => (f s, e)) }
  
/- CR clang: Maybe rename liftState{,Full} functions? -/
def NEStateM.liftStateFull (getter : σ → σ') (setter : σ' → σ → σ)
    (inner : NEStateM σ' ε α) : NEStateM σ ε α :=
  fun s => mapState (fun s' => setter s' s) (inner (getter s))

  /- CR clang: for now just spefify setter manually and ask leo later... -/
  /-
def NEStateM.liftState (getter : σ → σ') (inner : Exec σ' ε α) : Exec σ ε α :=
  /- CR clang for thibaut: So I'm not sure how to translate this
    liftSt_full getter (@setv _ _ getter _) inner.
  -/
  NEStateM.liftStateFull getter (fun s' s => sorry) inner
  -/

/-
def NEStateM.elemOfResults {E A} (x : A) (r : Res E A) : Prop :=
  x ∈ r.results
def NEStateM.elemOfResultsNoState {St E A} (x : A) (r : Res (St × E) (St × A)) : Prop :=
  x ∈ (r.results.map Prod.snd)
def NEStateM.elemOfResult {E A} (x : Except E A) (e : Res E A) : Prop :=
  match x with
  | .ok v => v ∈ e.results
  | .error err => err ∈ e.errors
def NEStateM.elemOfResultNoState {St E A} (x : Except E A) (e : Res (St × E) (St × A)) : Prop :=
  match x with
  | .ok v => v ∈ (e.results.map Prod.snd)
  | .error err => err ∈ (e.errors.map Prod.snd)
-/
def NEStateM.discardNone : Option α → NEStateM σ ε α
  | some a => pure a
  | none => discard
def NEStateM.mapError (f : ε → ε') (m : NEStateM σ ε α) : NEStateM σ ε' α :=
  fun s =>
    let res := m s
    { results := res.results, errors := res.errors.map (fun (s', e) => (s', f e)) }

end ExecutionMonad

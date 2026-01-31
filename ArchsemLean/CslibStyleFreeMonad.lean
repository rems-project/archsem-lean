/- Trying out cslib free monad. -/

/-
`u` is the universe of return variables.
`v` is the universe of effects
`w` is the universe of eventual return values
FreeM lives in a universe higher than all of these. But why exactly is this a problem?
-/
/-
inductive FreeM.{u, v, w} (F : Type u → Type v) (α : Type w) where
  | pure (a : α) : FreeM F α
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
 #check FreeM
-/
inductive FreeM.{v, w} (F : Type → Type v) (α : Type w) where
  | pure (a : α) : FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
 #check FreeM

/- our state is a signle natural number -/
/- effects are Type → Type because they are parameterised by their return value -/
/- I think this links to what me and Thibaut were talking about, where we are going
to do things differently from cslib. Because we can know the return type in advance
we are able to side-step some universe ascending madness. -/
inductive StateEff : Type → Type where
  | Get : StateEff Nat
  | Put : Nat → StateEff Unit
#check StateEff.Get
#check StateEff.Put 10

/-
In cslib an effect, `Type → Type`, can have arbitrary return type.
In archsem, an effect is `Type` along with an `Eff → Type` return type.
-/

/- Such a non-effect has no way to specify its return type. -/
inductive NonEff : Type where
  | Get : NonEff
  | Put : Nat → NonEff

inductive LogEff : Type → Type where
  | Log : String → LogEff Unit

inductive FSum (F G : Type → Type) : Type → Type
  | inl : F α → FSum F G α
  | inr : G α → FSum F G α

abbrev Eff := FSum StateEff LogEff

/- cslib test suite defines such helper functions as -/
def getState : FreeM Eff Nat := FreeM.liftBind (FSum.inl StateEff.Get) FreeM.pure
def setState (n : Nat) : FreeM Eff Unit := FreeM.liftBind (FSum.inl (StateEff.Put n)) FreeM.pure
def log (s : String) : FreeM Eff Unit := FreeM.liftBind (FSum.inr (LogEff.Log s)) FreeM.pure

def free_monad_bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β := match x with
  | FreeM.pure x => f x
  | FreeM.liftBind op cont => FreeM.liftBind op (fun r => free_monad_bind (cont r) f)

instance : Monad (FreeM F) where
  pure x := FreeM.pure x
  bind := free_monad_bind

def example_prog : FreeM Eff Nat := do
  log "starting..."
  setState 4
  let n ← getState
  log s!"checking if state is 4..."
  if n = 4 then setState 9 else setState n
  log s!"returning {n}..."
  FreeM.pure n

def verbose_prog : FreeM Eff Nat :=
  FreeM.liftBind
      (FSum.inl StateEff.Get)
      (fun n =>
        FreeM.liftBind
          (FSum.inr (LogEff.Log "hello"))
          (fun () =>
            FreeM.pure n
          )
      )

example : Sort 2 := FreeM Eff Nat

/- Notice that we have been able to write the example_prog before we have defined how
to evaluate the state and log effects. This is the separation of syntax from semantics
we are after. -/
#check example_prog

/- cslib calls this the "semantic domain". It is the type we would like to interpret
the free monad on effects as. Takes state, log, produces new state with new log and
return value. -/
abbrev EffAction (α : Type) := Nat → List String → Nat × List String × α

def eff_pure (x : α) : EffAction α := fun n l => (n, l, x)
def eff_step {α : Type} (op : Eff α) (cont : α → EffAction β) : EffAction β := match α, op with
  | _, FSum.inl StateEff.Get => fun σ l => cont σ σ l
  | _, FSum.inl (StateEff.Put n) => fun _ l => cont () n l
  | _, FSum.inr (LogEff.Log msg) => fun σ l => cont () σ (msg::l)

def foldFreeM (pure : {α : Type} → α → EffAction α) (step : {α β : Type} → Eff α → (α → EffAction β) → EffAction β) (mon : FreeM Eff γ) : EffAction γ :=
  match mon with
  | FreeM.pure x => pure x
  | FreeM.liftBind op cont => step op (fun y => foldFreeM pure step (cont y))

def interpreter : FreeM Eff α → EffAction α  :=
  foldFreeM eff_pure eff_step

#check interpreter example_prog
#eval (interpreter example_prog) 0 []
#eval (interpreter verbose_prog) 4 []


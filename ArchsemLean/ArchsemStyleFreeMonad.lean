/- Some experiments I'm doing with converting the archsem style free monad
to lean. Note its differences from the cslib style. -/

/-
(** The effect typeclass, declares a type as an effect and provide [eff_ret],
    the return type function. *)
Class Effect (Eff : eff) := eff_ret : Eff → Type@{e}.
-/
class Effect.{u, v} (α : Type u) where
  eff_ret : α → Type v

/-
(* Eff : eff. eff is the type universe of effects. *)
Inductive fMon {A : Type} :=
  | Ret (ret : A)
  | Next (call : Eff) (k : eff_ret call → fMon).
  Arguments fMon : clear implicits.
-/
/-
`u` is the universe of return variables.
`v` is the universe of effects
`w` is the universe of eventual return values
-/
inductive FreeM.{u, v, w} (Eff : Type v) [Effect.{v, u} Eff] (α : Type w) where
  | pure (a : α) : FreeM Eff α
  | bind (call : Eff) (cont : Effect.eff_ret call → FreeM Eff α) : FreeM Eff α
#check FreeM

inductive ExampleEff where
  | LogEff : String → ExampleEff
  | GetState : ExampleEff
  | PutState : Nat → ExampleEff

instance : Effect ExampleEff where
  eff_ret (eff : ExampleEff) := match eff with
    | .LogEff _ => Unit
    | .GetState => Nat
    | .PutState _ => Unit

#check FreeM ExampleEff Nat

def getState : FreeM ExampleEff Nat := FreeM.bind (ExampleEff.GetState) FreeM.pure
def setState (x : Nat) : FreeM ExampleEff Unit := FreeM.bind (ExampleEff.PutState x) FreeM.pure
def log (s : String) : FreeM ExampleEff Unit := FreeM.bind (ExampleEff.LogEff s) FreeM.pure

def free_monad_bind [Effect E] (x : FreeM E α) (f : α → FreeM E β) : FreeM E β := match x with
  | .pure x => f x
  | .bind call cont => FreeM.bind call (fun r => free_monad_bind (cont r) f)

instance [Effect E] : Monad (FreeM E) where
  pure x := FreeM.pure x
  bind := free_monad_bind

def example_prog : FreeM ExampleEff Nat := do
  log "starting..."
  setState 4
  let n ← getState
  log s!"checking if state is 4..."
  if n = 4 then setState 9 else setState n
  log s!"returning {n}..."
  FreeM.pure n

def verbose_prog : FreeM ExampleEff Nat :=
  FreeM.bind
      (ExampleEff.GetState)
      (fun n =>
        FreeM.bind
          (ExampleEff.LogEff "hello")
          (fun () =>
            FreeM.pure n
          )
      )

abbrev EffAction (α : Type) := Nat → List String → Nat × List String × α
def eff_pure (x : α) : EffAction α := fun n l => (n, l, x)
def eff_step (op : ExampleEff) (cont : Effect.eff_ret op → EffAction β): EffAction β := match op with
  | ExampleEff.GetState => fun σ l => cont σ σ l
  | ExampleEff.PutState n => fun _ l => cont () n l
  | ExampleEff.LogEff msg => fun σ l => cont () σ (msg::l)

def foldFreeM (pure : {α : Type} → α → EffAction α) (step : {β : Type} → (call : ExampleEff) → (Effect.eff_ret call → EffAction β) → EffAction β) (mon : FreeM ExampleEff γ) : EffAction γ :=
    match mon with
  | FreeM.pure x => pure x
  | FreeM.bind op cont => step op (fun y => foldFreeM pure step (cont y))

def interpreter : FreeM ExampleEff α → EffAction α  :=
  foldFreeM eff_pure eff_step

#check interpreter example_prog
#eval (interpreter example_prog) 0 []
#eval (interpreter verbose_prog) 4 []


import ArchSemTinyArm.Promising
import ArchSem.TerminatingModel
import Init.Data.List.Lemmas

open ArchSemTinyArm.Promising
open ArchSem.TerminatingModel
open ArchSem.NondeterministicMonad

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

section PromiseFirstProof

-- Common simplification bundle for NEStateM/NExcept proof scripts.
open Lean Elab Tactic Lean.Parser.Tactic

-- I've taken inspiration from https://github.com/leanprover-community/mathlib4/blob/8f1377de1fe0f57f74d9e3eddb3e1ed2e30a9cf9/Mathlib/Tactic/FieldSimp.lean
-- There is supprisingly little written about this online.
elab "simp_nestatem" loc:(location)? : tactic => do
  let loc := loc.getD (← `(location| at ⊢))
  evalTactic (← `(tactic| simp only [
    pure, bind, get, set, modify, modifyGet,
    NExcept.pure, NExcept.bind, NExcept.merge,
    NEStateM.pure, NEStateM.bind, 
    List.foldr, List.map, List.append_nil
  ] $loc))

theorem run_to_termination_monotonic_fuel
    (tid : Fin nThreads) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition nThreads)
    (fuel : Nat) (base : Nat) (promises : List Msg) (pstate : ProjectedModelState)
    : ∀ s ∈ (runToTermination tid initmem isem termination fuel base (promises, pstate)).oks,
        s.snd →
        s ∈ (runToTermination tid initmem isem termination (fuel + 1) base (promises, pstate)).oks
  := by
  induction fuel generalizing promises pstate with
  | zero =>
    simp only [runToTermination, Prod.forall, Bool.forall_bool, Bool.false_eq_true,
      false_implies, implies_true, forall_const, true_and]
    intros
    contradiction
  | succ f ih =>
    intro s h fuelRemains
    rw [runToTermination] at h ⊢
    simp only [Bind.bind] at h ⊢
    rw [NEStateM.bind_iff] at h ⊢
    rcases h with ⟨s', a', h_interp, h⟩
    refine ⟨s', a', h_interp, ?_⟩
    simp_nestatem at h ⊢
    split at h
    case succ.isFalse h_termination =>
      simp only [h_termination, Bool.false_eq_true, ↓reduceIte]
      simp_nestatem at h ⊢
      exact ih s'.fst
        { threadState := s'.snd.threadState, mem := s'.snd.mem, iis := IIS.init }
        s h fuelRemains
    case succ.isTrue h_termination =>
      simp only [h_termination, ↓reduceIte]
      assumption

theorem run_to_termination_stays_terminated
    (tid : Fin nThreads) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition nThreads)
    (fuel : Nat) (base : Nat) (promises₀ : List Msg) (pstate₀ : ProjectedModelState)
      : ( ∀ (promises : List Msg) (pstate : ProjectedModelState),
          ((promises, pstate), false)
          ∉ (runToTermination tid initmem isem termination fuel base (promises₀, pstate₀)).oks )
      → ( ∀ (promises : List Msg) (pstate : ProjectedModelState),
          ((promises, pstate), false)
          ∉ (runToTermination tid initmem isem termination (fuel + 1) base (promises₀, pstate₀)).oks )
  := by
  induction fuel generalizing promises₀ pstate₀ with
  | zero =>
    intro h
    simp [runToTermination, pure, NEStateM.pure, NExcept.pure] at h
  | succ f ih =>
    intro h promises pstate
    rw [runToTermination] at h ⊢
    simp only [Bind.bind] at h ⊢
    simp only [NEStateM.bind_iff] at h ⊢
    simp_nestatem at h ⊢

    simp only [not_exists, not_and] at ⊢ h
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_imp,
      forall_eq_apply_imp_iff, forall_eq] at h ⊢

    intro (interp_promises, interp_pstate) () h_interp
    split <;> simp_nestatem ; try simp
    apply ih
    intro promises' pstate'
    specialize h promises' pstate' (interp_promises, interp_pstate) () h_interp
    split at h <;> simp_nestatem at h
    · contradiction
    · assumption

theorem enumerate_result_promises_monotonic_fuel
    (fuel : Nat) (tid : Fin nThreads) (initmem : InitialMem) (isem : SailM Unit)
    (termCond : TerminationCondition nThreads) (ts : ThreadState) (mem : PromisingMemory)
    : ∀ s ∈ (enumerateResults fuel tid initmem isem termCond ts mem).promises,
        ¬(enumerateResults fuel tid initmem isem termCond ts mem).out_of_fuel →
        s ∈ (enumerateResults (fuel + 1) tid initmem isem termCond ts mem).promises ∧
        ¬(enumerateResults (fuel + 1) tid initmem isem termCond ts mem).out_of_fuel
  := by
  intro s
  simp only [enumerateResults]
  simp [List.mem_eraseDups] -- TODO: using simp like this is bad practice.
  intro promises pmstate h h_s_in_promises h_fuel_remains
  cases h with
  | inl h =>
    specialize h_fuel_remains promises pmstate
    contradiction
  | inr h =>
    apply And.intro
    case left =>
      exists promises
      refine ⟨?_, h_s_in_promises⟩
      exists pmstate
      have := run_to_termination_monotonic_fuel tid initmem isem termCond fuel
        (List.length mem) [] { threadState := ts, mem := mem, iis := IIS.init }
        ((promises, pmstate), true) h
      simp [this]
    case right =>
      exact run_to_termination_stays_terminated tid initmem isem termCond fuel (List.length mem)
        [] { threadState := ts, mem := mem, iis := IIS.init } h_fuel_remains

theorem promise_select_tid_monotonic_fuel
    (fuel : Nat) (mstate : ModelState nThreads) (tid : Fin nThreads) (isem : SailM Unit)
    (termCond : TerminationCondition nThreads)
    : ∀ s ∈ (promiseSelectTid fuel mstate tid isem termCond).oks,
        s ∈ (promiseSelectTid (fuel + 1) mstate tid isem termCond).oks
  := by
  simp only [promiseSelectTid]
  intro msg h
  split at h <;> try contradiction
  rename_i h_is_false
  obtain ⟨h_l, h_r⟩ := enumerate_result_promises_monotonic_fuel fuel tid mstate.initmem
    isem termCond mstate.threadStates[tid] mstate.mem msg h h_is_false
  simp only [h_r, Bool.false_eq_true, ↓reduceIte, NExcept.choose, h_l]

theorem run_step_monotonic_fuel
   (fuel : Nat) (isem : SailM Unit) (termCond : TerminationCondition nThreads)
   (pState : ModelState nThreads)
   : ∀ s ∈ (runStep fuel isem termCond pState).oks,
       s ∈ (runStep (fuel + 1) isem termCond pState).oks
 := by
 simp only [runStep, promiseTid]
 intro (mstate, ()) h
 simp only [Bind.bind, NEStateM.bind_iff] at h ⊢
 rcases h with ⟨s₁, s₂, h_get, s₃, tid, h_choose, h⟩
 exists s₁, s₂, h_get, s₃, tid, h_choose
 split at h <;> try contradiction
 rename_i h_terminated
 simp only [h_terminated, Bool.false_eq_true, ↓reduceIte]
 simp only [NEStateM.bind_iff, Fin.exists_fin_two, Fin.isValue] at h ⊢
 rcases h with ⟨s₁, h⟩
 exists s₁
 rcases h with ⟨h_get₁, s₂, s₃, h_get₂, s₄, msg, h_prom, h_mod⟩ | ⟨h⟩
 case inl =>
   apply Or.inl
   refine ⟨h_get₁, s₂, s₃, h_get₂, s₄, msg, ?_⟩
   simp only [liftM, monadLift, MonadLift.monadLift, List.mem_map,
     Prod.mk.injEq, exists_eq_right_right] at h_prom ⊢
   have := promise_select_tid_monotonic_fuel fuel s₃ tid isem termCond msg h_prom.1
   simp [this, h_prom.2, h_mod]
 case inr =>
   exact Or.inr h

-- TODO: be consistent with pstate/pState naming.

theorem naive_runtime_monotonic_fuel
    : ∀ (pState : ModelState nThreads) (fuel : Nat),
      ∀ r ∈ (runNaive fuel isem nThreads termCond pState).oks,
        r ∈ (runNaive (fuel + 1) isem nThreads termCond pState).oks
  := by
  intro pState fuel (promises, mstate) h
  induction fuel generalizing pState with
  | zero => contradiction
  | succ f ih =>
    rw [runNaive] at h ⊢
    simp only [Bind.bind, NEStateM.bind_iff] at h ⊢
    rcases h with ⟨s₁, s₂, h_get, h⟩
    refine ⟨s₁, s₂, h_get, ?_⟩
    split at h
    case isFalse h_term =>
      simp only [h_term, ↓reduceDIte]
      rw [NEStateM.bind_iff] at h ⊢
      rcases h with ⟨s₃, u, h_step, h_recurse⟩
      have h_l := run_step_monotonic_fuel (f + 1) isem termCond s₁ (s₃, u) h_step
      have h_r := ih s₃ h_recurse
      exact ⟨s₃, u, h_l, h_r⟩
    case isTrue h_term =>
      simp [h_term, h]

end PromiseFirstProof

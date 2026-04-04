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
      intro h
      cases h with
      | inl h =>
        simp [h]
      | inr h =>
        rw [ih] at h
        simp [h]
    case mpr =>
      intro h
      rcases h with ⟨a, h_in, h_in_ok⟩
      cases h_in with
      | head =>
        simp [h_in_ok]
      | tail _ h_in_tail =>
        apply Or.inr
        apply ih.mpr
        exact ⟨a, h_in_tail, h_in_ok⟩

theorem NEStateM.bind_iff {ε σ α β} (s₀ : σ) (s : σ) (b : β) (m : NEStateM ε σ α) (f : α → NEStateM ε σ β)
    : (s, b) ∈ (NEStateM.bind m f s₀).oks ↔ ∃ (s' : σ) (a : α), (s', a) ∈ (m s₀).oks ∧ (s, b) ∈ (f a s').oks
  := by
  simp [Bind.bind, NEStateM.bind]
  have base := @NExcept.bind_iff (σ × ε) (σ × α) (σ × β) (s, b) (m s₀) (fun p => f p.snd p.fst)
  conv => lhs ; lhs ; rhs ; rhs ; intro p
  conv at base => rhs ; simp
  exact base

section PromiseFirstProof

-- Common simplification bundle for NEStateM/NExcept proof scripts.
open Lean Elab Tactic Lean.Parser.Tactic

-- I've taken inspiration from https://github.com/leanprover-community/mathlib4/blob/8f1377de1fe0f57f74d9e3eddb3e1ed2e30a9cf9/Mathlib/Tactic/FieldSimp.lean
-- There is supprisingly little written about this online.
elab "simp_nestatem" loc:(location)? : tactic => do
  let loc := loc.getD (← `(location| at ⊢))
  evalTactic (← `(tactic| simp only [
    pure, bind, get, set, modify, modifyGet,
    NExcept.pure, NEStateM.bind,  NExcept.bind, NExcept.pure, NExcept.merge,
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
    simp [runToTermination]
    intros
    contradiction
  | succ f ih =>
    intro s mem fuelRemains
    simp only [runToTermination, Bind.bind] at mem
    repeat rw [NEStateM.bind_iff] at mem
    rcases mem with ⟨s', a', h_interp, h⟩
    simp_nestatem at h
    rw [runToTermination]
    simp only [Bind.bind]
    repeat rw [NEStateM.bind_iff]
    refine ⟨s', a', h_interp, ?_⟩
    simp_nestatem
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
    simp [runToTermination, pure, NExcept.pure] at h
  | succ f ih =>
    intro h promises pstate
    rw [runToTermination.eq_def] at h ⊢
    simp only at h ⊢
    simp [Bind.bind] at h ⊢
    repeat simp only [NEStateM.bind_iff] at h ⊢
    simp_nestatem at h ⊢

    simp only [not_exists, not_and] at ⊢ h
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_imp,
      forall_eq_apply_imp_iff, forall_eq] at h ⊢

    intro (interp_promises, interp_pstate) () h_interp
    split
    case isTrue =>
      simp_nestatem
      simp
    case isFalse =>
      simp_nestatem
      apply ih
      intro promises' pstate'
      specialize h promises' pstate' (interp_promises, interp_pstate) () h_interp
      split at h
      case a.isTrue =>
        simp_nestatem at h
        contradiction
      case a.isFalse =>
        simp_nestatem at h
        assumption

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
  have h_base := run_to_termination_monotonic_fuel tid initmem isem termCond fuel
    (List.length mem) [] { threadState := ts, mem := mem, iis := IIS.init }
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
      specialize h_base ((promises, pmstate), true)
      have := h_base h
      simp [h_base h]
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
  split at h
  case isTrue =>
    contradiction
  case isFalse h_is_false =>
    simp only [NExcept.choose] at h
    have := enumerate_result_promises_monotonic_fuel fuel tid mstate.initmem
      isem termCond mstate.threadStates[tid] mstate.mem msg h h_is_false
    rcases this with ⟨h_l, h_r⟩
    simp only [h_r, Bool.false_eq_true, ↓reduceIte, NExcept.choose, h_l]

theorem run_step_monotonic_fuel
   : ∀ (pState : ModelState nThreads) (fuel : Nat),
     ∀ s ∈ (runStep fuel isem termCond pState).oks,
       s ∈ (runStep (fuel + 1) isem termCond pState).oks
 := by
 sorry

theorem naive_runtime_monotonic_fuel
    : ∀ (pState : ModelState nThreads) (fuel : Nat),
      ∀ r ∈ (runNaive fuel isem nThreads termCond pState).oks,
        r ∈ (runNaive (fuel + 1) isem nThreads termCond pState).oks
  := by
  intro pState fuel r mem
  simp [runNaive] at mem ⊢

  simp [Bind.bind, NEStateM.bind] at ⊢
  sorry

end PromiseFirstProof

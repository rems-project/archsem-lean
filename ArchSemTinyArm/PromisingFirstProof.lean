import Init.Data.List.Lemmas
import ArchSem.TerminatingModel
import ArchSemTinyArm.Promising

open ArchSem.NondeterministicMonad
open ArchSem.TerminatingModel
open ArchSemTinyArm.Promising

theorem NEStateM.bind_mono {m₁ m₂ : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m₁ s).oks, sa ∈ (m₂ s).oks)
    → (∀ sa ∈ (m₁ s).oks, sb ∈ (f₁ sa.snd sa.fst).oks → sb ∈ (f₂ sa.snd sa.fst).oks)
    → (sb ∈ (Bind.bind m₁ f₁ s).oks → sb ∈ (Bind.bind m₂ f₂ s).oks)
  := by
  intro h_m h_f h
  simp only [Bind.bind] at h ⊢
  rw [NEStateM.bind_iff'] at h ⊢
  obtain ⟨sa, h_sa, h⟩ := h
  refine ⟨sa, h_m sa h_sa, h_f sa h_sa h⟩

theorem NEStateM.bind_mono_right {m : NEStateM ε σ α} {f₁ f₂ : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m s).oks, sb ∈ (f₁ sa.snd sa.fst).oks → sb ∈ (f₂ sa.snd sa.fst).oks)
    → (sb ∈ (Bind.bind m f₁ s).oks → sb ∈ (Bind.bind m f₂ s).oks)
  := by
  intro h_f
  exact NEStateM.bind_mono (by simp) h_f

theorem NEStateM.bind_mono_left {m₁ m₂ : NEStateM ε σ α} {f : α → NEStateM ε σ β} {s : σ} {sb : σ × β}
    : (∀ sa ∈ (m₁ s).oks, sa ∈ (m₂ s).oks)
    → (sb ∈ (Bind.bind m₁ f s).oks → sb ∈ (Bind.bind m₂ f s).oks)
  := by
  intro h_m
  exact NEStateM.bind_mono h_m (by simp)

theorem NEStateM.bind_get_elim {f : σ → NEStateM ε σ β} {s : σ}
    : Bind.bind get f s = f s s
  := by
  simp [
    bind, get,
    NEStateM.get, NEStateM.bind,
    NExcept.pure, NExcept.bind, NExcept.merge
  ]

theorem NEStateM.bind_modify_elim {f : Unit → NEStateM ε σ β} {h : σ → σ} {s : σ}
    : Bind.bind (modify h) f s = f () (h s)
  := by
  simp [
    bind, modify, modifyGet,
    NEStateM.bind, 
    NExcept.pure, NExcept.bind, NExcept.merge
  ]

namespace ArchSemTinyArm.Promising

-- Common simplification bundle for NEStateM/NExcept proof scripts.
open Lean Elab Tactic Lean.Parser.Tactic

/- TODO: remove
/-
TODO: This custom tactic is a bit brute force. Lets make it more precise.

I've taken inspiration from https://github.com/leanprover-community/mathlib4/blob/8f1377de1fe0f57f74d9e3eddb3e1ed2e30a9cf9/Mathlib/Tactic/FieldSimp.lean
There is supprisingly little written about this online.
-/
elab "simp_nestatem" loc:(location)? : tactic => do
  let loc := loc.getD (← `(location| at ⊢))
  evalTactic (← `(tactic| simp only [
    pure, bind, get, set, modify, modifyGet,
    NExcept.pure, NExcept.bind, NExcept.merge,
    NEStateM.pure, NEStateM.bind, 
    List.foldr, List.map, List.append_nil
  ] $loc))
  -/

theorem run_to_termination_monotonic_fuel
    {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termination : TerminationCondition nThreads}
    {fuel base : Nat} {promises : List Msg} {pstate : ProjectedModelState}
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
    revert h
    rw [runToTermination, runToTermination]
    apply NEStateM.bind_mono_right
    intro (s', a') h_interp
    simp only [NEStateM.bind_get_elim]
    intro h
    split at h
    case isFalse h_termination =>
      simp only [h_termination, Bool.false_eq_true, ↓reduceIte]
      simp only [NEStateM.bind_modify_elim] at h ⊢
      exact ih s h fuelRemains
    case isTrue h_termination =>
      simp only [h_termination, ↓reduceIte]
      assumption


/-
CR clang: This proof is made awkward by the fact that
runToTermination returns a structre marked with noFuel instead
of using an except...
-/
theorem run_to_termination_stays_terminated
    {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termination : TerminationCondition nThreads}
    {fuel : Nat} {base : Nat} {promises₀ : List Msg} {pstate₀ : ProjectedModelState}
      : ( ∀ (promises : List Msg) (pstate : ProjectedModelState),
          ((promises, pstate), false)
          ∉ (runToTermination tid initmem isem termination fuel base (promises₀, pstate₀)).oks )
      → ( ∀ (promises : List Msg) (pstate : ProjectedModelState),
          ((promises, pstate), false)
          ∉ (runToTermination tid initmem isem termination (fuel + 1) base (promises₀, pstate₀)).oks )
  := by
  -- Apply contrapositive to get in terms of `∃. ∈`
  intro h
  simp only [← not_exists] at h ⊢
  revert h
  apply mt
  
  induction fuel generalizing promises₀ pstate₀ with
  | zero =>
    intro h
    simp [runToTermination, pure, NEStateM.pure, NExcept.pure]
  | succ f ih =>
    rw [runToTermination, runToTermination]
    simp
    apply NEStateM.bind_mono_right
    
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

theorem enumerate_results_stays_terminated {nThreads : Nat}
    {fuel : Nat} {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termCond : TerminationCondition nThreads} {ts : ThreadState} {mem : PromisingMemory}
    : ¬(enumerateResults nThreads fuel tid initmem isem termCond ts mem).outOfFuel →
      ¬(enumerateResults nThreads (fuel + 1) tid initmem isem termCond ts mem).outOfFuel
  := by
  simp only [enumerateResults, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Prod.exists,
    exists_eq_right, not_exists]
  apply run_to_termination_stays_terminated

theorem enumerate_result_promises_monotonic_fuel {nThreads : Nat}
    {fuel : Nat} {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termCond : TerminationCondition nThreads} {ts : ThreadState} {mem : PromisingMemory}
    : ∀ s ∈ (enumerateResults nThreads fuel tid initmem isem termCond ts mem).promises,
        ((enumerateResults nThreads fuel tid initmem isem termCond ts mem).outOfFuel = false) →
        s ∈ (enumerateResults nThreads (fuel + 1) tid initmem isem termCond ts mem).promises ∧
        ((enumerateResults nThreads (fuel + 1) tid initmem isem termCond ts mem).outOfFuel = false)
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
      exact Or.inr (run_to_termination_monotonic_fuel _ h (by simp))
    case right =>
      exact run_to_termination_stays_terminated h_fuel_remains

theorem enumerate_results_eual {nThreads : Nat}
    {fuel : Nat} {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termCond : TerminationCondition nThreads} {ts : ThreadState} {mem : PromisingMemory}
    : ((enumerateResults nThreads fuel tid initmem isem termCond ts mem).outOfFuel = false) →
      (enumerateResults nThreads fuel tid initmem isem termCond ts mem)
      = (enumerateResults nThreads (fuel + 1) tid initmem isem termCond ts mem)
  := by
  intro h_fuel
  simp only [enumerateResults]
  sorry

theorem promise_select_tid_monotonic_fuel
    {fuel : Nat} {mstate : ModelState nThreads} {tid : Fin nThreads} {isem : SailM Unit}
    {termCond : TerminationCondition nThreads}
    : ∀ s ∈ (promiseSelectTid fuel mstate tid isem termCond).oks,
        s ∈ (promiseSelectTid (fuel + 1) mstate tid isem termCond).oks
  := by
  simp only [promiseSelectTid]
  intro msg h
  split at h <;> try contradiction
  rename_i h_is_false
  simp only [Bool.not_eq_true] at h_is_false
  obtain ⟨h_l, h_r⟩ := enumerate_result_promises_monotonic_fuel msg h h_is_false
  simp only [h_r, Bool.false_eq_true, ↓reduceIte, NExcept.choose, h_l]

theorem run_step_monotonic_fuel
    {fuel : Nat} {isem : SailM Unit} {termCond : TerminationCondition nThreads}
    {pState : ModelState nThreads}
    : ∀ s ∈ (runStep fuel isem termCond pState).oks,
        s ∈ (runStep (fuel + 1) isem termCond pState).oks
  := by
  simp only [runStep, promiseTid]
  intro (mstate, ())

  apply NEStateM.bind_mono_right
  intro (s₁, s₂) h_get
  apply NEStateM.bind_mono_right
  intro (s₃, tid) h_choose

  intro h
  split at h <;> try contradiction
  rename_i h_terminated

  revert h
  simp only [h_terminated, Bool.false_eq_true, ↓reduceIte]
  apply NEStateM.bind_mono_right
  intro (s₁, choice) h_choice

  match choice with
  | 0 =>
    simp only [NEStateM.bind_get_elim]
    apply NEStateM.bind_mono_left
    simp only [liftM, monadLift, MonadLift.monadLift]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.mk.injEq,
      true_and, exists_eq_right]
    apply promise_select_tid_monotonic_fuel
  | 1 =>
    simp []

-- TODO: be consistent with pstate/pState naming.

theorem naive_runtime_monotonic_fuel {fuel : Nat} {isem : SailM Unit} {nThreads : Nat}
    {termCond : TerminationCondition nThreads} {pState : ModelState nThreads} 
    : ∀ r ∈ (runNaive fuel isem nThreads termCond pState).oks,
        r ∈ (runNaive (fuel + 1) isem nThreads termCond pState).oks
  := by
  intro (promises, mstate)
  induction fuel generalizing pState with
  | zero =>
    rw [runNaive]
    intros
    contradiction
  | succ f ih =>
    rw [runNaive, runNaive]

    apply NEStateM.bind_mono_right
    intro (s₁, s₂) h_get
    
    split
    case isFalse h_term =>
      apply NEStateM.bind_mono
      · apply run_step_monotonic_fuel
      · intro pState _ ; apply ih
    case isTrue h_term =>
      simp

theorem promise_first_runtime_monotonic_fuel {fuel : Nat} {isem : SailM Unit} {nThreads : Nat}
    {termCond : TerminationCondition nThreads} {pState : ModelState nThreads} 
    : ∀ r ∈ (runPromiseFirst fuel isem nThreads termCond pState).oks,
        r ∈ (runPromiseFirst (fuel + 1) isem nThreads termCond pState).oks
  := by
  intro (promises, mstate) h
  induction fuel generalizing pState with
  | zero =>
    rw [runPromiseFirst] at h
    contradiction
  | succ f ih =>
    rw [runPromiseFirst] at h ⊢
    simp only [Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte] at h ⊢
    simp only [Bind.bind, NEStateM.bind_iff] at h ⊢
    rcases h with ⟨s₁, s_enum, h_get, h⟩
    refine ⟨s₁, s_enum, h_get, ?_⟩
    split at h <;> try contradiction
    split <;> rename_i h_fuel h_fuel'
    <;> simp only [Nat.add_one_sub_one, Fin.getElem_fin, Vector.any_toList, Vector.any_eq_true,
          Vector.getElem_ofFn, not_exists, Bool.not_eq_true, Vector.any_eq_true] at h_fuel h_fuel'
    case isTrue =>
      rcases h_fuel' with ⟨tid, h_tid, h_fuel'⟩
      specialize h_fuel tid h_tid
      apply absurd h_fuel'
      apply enumerate_results_stays_terminated
      simp [h_fuel]
    case isFalse =>
      simp only [NEStateM.bind_iff] at h ⊢
      rcases h with ⟨s₁, u, h_u, s_match, c, h_c, h⟩
      refine ⟨s₁, u, h_u, s_match, c, h_c, ?_⟩
      split at h
      case h_1 => -- make promise
        simp only [NEStateM.bind_iff] at h ⊢
        rcases h with ⟨s₁, tid, h_choose_tid, s₂, msg, h_choose_ev, s₃, u, h_mod, h⟩
        refine ⟨s₁, tid, h_choose_tid, s₂, msg, ?_⟩
        simp only [NEStateM.choose, NExcept.choose] at h_choose_ev ⊢
        simp only [Nat.add_one_sub_one, List.mem_map, Prod.mk.injEq, exists_eq_right_right] at h_choose_ev ⊢
        simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at h_choose_ev ⊢
        specialize h_fuel tid.val tid.isLt
        -- TODO: maybe I should make theorem arguments implicit
        have := enumerate_result_promises_monotonic_fuel _ h_choose_ev.left h_fuel
        exact ⟨⟨this.left, h_choose_ev.right⟩, s₃, u, h_mod, ih h⟩
      case h_2 => -- terminate
        simp only [NEStateM.bind_iff] at h ⊢
        rcases h with ⟨s₁, threads, h_enumerate, h⟩
        -- TODO: Here I need to use enumerate_result_final_states_equal
        -- the order matters because we use mapM
        -- Or maybe just write theorem for enumerate_results_equal
        have := enumerate_result_promises_monotonic_fuel
        refine ⟨s₁, threads, h_enumerate, ?_⟩
      case h_3 => -- 
      
    case isFalse h_term =>
      simp only [h_term, ↓reduceDIte]
      rw [NEStateM.bind_iff] at h ⊢
      rcases h with ⟨s₃, u, h_step, h_recurse⟩
      have h_l := run_step_monotonic_fuel (f + 1) isem termCond s₁ (s₃, u) h_step
      have h_r := ih s₃ h_recurse
      exact ⟨s₃, u, h_l, h_r⟩
    case isTrue h_term =>
      simp [h_term, h]

theorem naive_model_monotonic_fuel {isem : SailM Unit} {fuel : Nat}
    : (createNaiveModel isem fuel).weaker (createNaiveModel isem (fuel + 1))
  := by
  rw [ComputationalTerminatingModel.weaker]
  intro nThreads termCond init final t r h r_eq
  rw [createNaiveModel, promisingRuntimeToModel, r_eq] at h ⊢
  simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, false_or] at h ⊢
  simp only [List.mem_eraseDups, List.mem_map] at h ⊢
  rcases h with ⟨r, h, h_eq⟩
  refine ⟨r, ?_, h_eq⟩
  apply naive_runtime_monotonic_fuel
  exact h

theorem naive_monotonic_fuel_full {isem : SailM Unit} {fuel : Nat}
    : ∀ fuel' ≥ fuel,
    (createNaiveModel isem fuel).weaker (createNaiveModel isem (fuel' + 1))
  := by
  intro fuel' h
  let d := fuel' - fuel
  have h_fuel'_eq : fuel' = fuel + d := by omega
  rw [h_fuel'_eq]
  induction d with
  | zero =>
    exact naive_model_monotonic_fuel
  | succ k ih =>
    exact ComputationalTerminatingModel.weaker_transitive ih naive_model_monotonic_fuel

end ArchSemTinyArm.Promising

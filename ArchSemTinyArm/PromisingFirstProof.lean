-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

import Init.Data.List.Lemmas
import ArchSem.TerminatingModel
import ArchSemTinyArm.Promising

open ArchSem.NondeterministicMonad
open ArchSem.TerminatingModel
open ArchSemTinyArm.Promising

namespace ArchSemTinyArm.Promising

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
    simp only [get, NEStateM.bind_get_elim]
    intro h
    split at h
    case isFalse h_termination =>
      simp only [h_termination, Bool.false_eq_true, ↓reduceIte]
      simp only [NEStateM.bind_modify_elim] at h ⊢
      exact ih s h fuelRemains
    case isTrue h_termination =>
      simp only [h_termination, ↓reduceIte]
      assumption


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
    rintro ⟨proms, s, h⟩
    rw [runToTermination] at h ⊢
    simp only [NEStateM.bind_iff] at h ⊢
    obtain ⟨w₁, u, h_w₁, w₂, w₂', h_w₂, h⟩ := h
    split at h <;> try contradiction
    rename_i h_term
    simp only [NEStateM.bind_modify_elim] at h
    obtain ⟨proms', s', h⟩ := ih ⟨proms, s, h⟩
    refine ⟨proms', s', w₁, u, h_w₁, w₂, w₂', h_w₂, ?_⟩
    simp only [h_term, Bool.false_eq_true, ↓reduceIte]
    simp only [NEStateM.bind_modify_elim]
    exact h

theorem run_to_termination_eventually_equal
    {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termination : TerminationCondition nThreads}
    {fuel base : Nat} {promises : List Msg} {pstate : ProjectedModelState}
    : (∀ s ∈ (runToTermination tid initmem isem termination fuel base (promises, pstate)).oks, s.snd)
     → runToTermination tid initmem isem termination fuel base (promises, pstate)
     = runToTermination tid initmem isem termination (fuel + 1) base (promises, pstate)
  := by
  intro h_term
  induction fuel generalizing promises pstate with
  | zero =>
    simp [runToTermination, pure, NEStateM.pure, NExcept.pure] at h_term
  | succ f ih =>
    rw [runToTermination, runToTermination]
    rw [runToTermination] at h_term

    apply NEStateM.bind_app_congr <;> try simp
    intro p₁ s₁ u₁ h_interp
    simp only [get, NEStateM.bind_get_elim]
    split <;> try simp
    rename_i h_term'

    apply NEStateM.bind_app_congr <;> try simp
    intro p₂ s₂ u₂ h_mod
    apply ih
    intro s h
    apply h_term
    rw [NEStateM.bind_iff]
    refine ⟨(p₁, s₁), u₁, h_interp, ?_⟩
    simp only [get, NEStateM.bind_get_elim, h_term', Bool.false_eq_true, ↓reduceIte]
    rw [NEStateM.bind_iff]
    refine ⟨(p₂, s₂), u₂, h_mod, h⟩

theorem run_to_termination_eventually_equal'
    {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termination : TerminationCondition nThreads}
    {fuel base : Nat} {promises : List Msg} {pstate : ProjectedModelState}
    : (∀ (p : List Msg) (s : ProjectedModelState),
        ((p, s), false) ∉ (runToTermination tid initmem isem termination fuel base (promises, pstate)).oks)
     → runToTermination tid initmem isem termination fuel base (promises, pstate)
     = runToTermination tid initmem isem termination (fuel + 1) base (promises, pstate)
  := by
  intro h
  apply run_to_termination_eventually_equal
  simp [h]


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

theorem enumerate_results_eventually_eual {nThreads : Nat}
    {fuel : Nat} {tid : Fin nThreads} {initmem : InitialMem} {isem : SailM Unit}
    {termCond : TerminationCondition nThreads} {ts : ThreadState} {mem : PromisingMemory}
    : ((enumerateResults nThreads fuel tid initmem isem termCond ts mem).outOfFuel = false) →
      (enumerateResults nThreads fuel tid initmem isem termCond ts mem)
      = (enumerateResults nThreads (fuel + 1) tid initmem isem termCond ts mem)
  := by
  intro h_fuel
  simp only [enumerateResults] at h_fuel ⊢
  simp [List.any_eq_false] at h_fuel
  have := run_to_termination_eventually_equal' h_fuel
  rw [this]

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
    simp only [get, NEStateM.bind_get_elim]
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
  intro (promises, mstate)
  induction fuel generalizing pState with
  | zero =>
    intro h
    rw [runPromiseFirst] at h
    contradiction
  | succ f ih =>
    rw [runPromiseFirst, runPromiseFirst]
    simp only [Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte]
    simp only [get, NEStateM.bind_get_elim]
    intro h
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
      have h_enum_eq (tid : Fin nThreads) := enumerate_results_eventually_eual (h_fuel tid.val tid.isLt)
      revert h
      apply NEStateM.bind_mono_right
      intro w₁ h_w₁
      apply NEStateM.bind_mono_right
      intro w₂ h_w₂

      match w₂.snd with
      | 0 => -- make promise
        simp only [Nat.add_one_sub_one, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
        apply NEStateM.bind_mono_right
        intro w₃ h_w₃
        apply NEStateM.bind_mono
        · simp [h_enum_eq]
        · intro w₄ h_w₄
          simp [NEStateM.bind_modify_elim]
          apply ih
      | 1 => -- terminate
        simp [h_enum_eq]
      | 2 => 
        simp [h_enum_eq]

-- TODO: remove lots of repetition from here onwards:

theorem naive_model_monotonic_fuel {isem : SailM Unit} {fuel : Nat}
    : (createNaiveModel isem fuel).weaker (createNaiveModel isem (fuel + 1))
  := by
  rw [ComputationalTerminatingModel.weaker]
  intro nThreads termCond init final t r h r_eq
  rw [createNaiveModel, promisingRuntimeToModel, r_eq] at h ⊢
  simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, false_or] at h ⊢
  simp only [Std.HashSet.mem_toList, Std.HashSet.mem_ofList] at h ⊢
  simp only [List.contains_eq_mem, List.mem_map, decide_eq_true_eq] at h ⊢
  rcases h with ⟨r, h, h_eq⟩
  refine ⟨r, ?_, h_eq⟩
  apply naive_runtime_monotonic_fuel
  exact h

theorem promise_first_model_monotonic_fuel {isem : SailM Unit} {fuel : Nat}
    : (createPromiseFirstModel isem fuel).weaker (createPromiseFirstModel isem (fuel + 1))
  := by
  rw [ComputationalTerminatingModel.weaker]
  intro nThreads termCond init final t r h r_eq
  rw [createPromiseFirstModel, promisingRuntimeToModel, r_eq] at h ⊢
  simp only [List.mem_append, List.mem_map, reduceCtorEq, and_false, exists_false, false_or] at h ⊢
  simp only [Std.HashSet.mem_toList, Std.HashSet.mem_ofList] at h ⊢
  simp only [List.contains_eq_mem, List.mem_map, decide_eq_true_eq] at h ⊢
  rcases h with ⟨r, h, h_eq⟩
  refine ⟨r, ?_, h_eq⟩
  apply promise_first_runtime_monotonic_fuel
  exact h

theorem naive_promising_monotonic_fuel_full {isem : SailM Unit} {fuel : Nat}
    : ∀ fuel' ≥ fuel,
    (createNaiveModel isem fuel).weaker (createNaiveModel isem fuel')
  := by
  intro fuel' h
  let d := fuel' - fuel
  have h_fuel'_eq : fuel' = fuel + d := by omega
  rw [h_fuel'_eq]
  induction d with
  | zero =>
    apply ComputationalTerminatingModel.weaker_refl
  | succ k ih =>
    exact ComputationalTerminatingModel.weaker_transitive ih naive_model_monotonic_fuel

theorem promise_first_monotonic_fuel_full {isem : SailM Unit} {fuel : Nat}
    : ∀ fuel' ≥ fuel,
    (createPromiseFirstModel isem fuel).weaker (createPromiseFirstModel isem fuel')
  := by
  intro fuel' h
  let d := fuel' - fuel
  have h_fuel'_eq : fuel' = fuel + d := by omega
  rw [h_fuel'_eq]
  induction d with
  | zero =>
    apply ComputationalTerminatingModel.weaker_refl
  | succ k ih =>
    exact ComputationalTerminatingModel.weaker_transitive ih promise_first_model_monotonic_fuel

end ArchSemTinyArm.Promising

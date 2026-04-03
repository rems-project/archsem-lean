import ArchSemTinyArm.Promising
import ArchSem.TerminatingModel

open ArchSemTinyArm.Promising
open ArchSem.TerminatingModel
open ArchSem.NondeterministicMonad

theorem NExcept.bind_iff {ε α β} (b : β) (m : NExcept ε α) (f : α → NExcept ε β)
     : b ∈ (NExcept.bind m f).oks ↔ ∃ (a : α), a ∈ m.oks ∧ b ∈ (f a).oks
  := by
  simp only [NExcept.bind]
  induction m.oks
  case nil =>
    apply Iff.intro
    all_goals simp
  case cons tail ih =>
    simp only [NExcept.merge, List.foldr, List.map, List.mem_append]
    apply Iff.intro
    case mp =>
      intro h
      cases h
      case inl h =>
        simp [h]
      case inr h =>
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

variable (isem : SailM Unit) (nThreads : Nat) (termCond : TerminationCondition nThreads)

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
    (promises : List Msg) (pstate : ProjectedModelState) (tid : Fin nThreads) (initmem : InitialMem)
    (fuel : Nat)
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
    case succ.isFalse =>
      simp_nestatem at h
      split
      case isFalse =>
        simp_nestatem
        exact ih s'.fst
          { threadState := s'.snd.threadState, mem := s'.snd.mem, iis := IIS.init }
          s h fuelRemains
      case isTrue =>
        contradiction
    case succ.isTrue =>
      split
      case isFalse =>
        contradiction
      case isTrue =>
        assumption

theorem enumerate_result_promises_monotonic_fuel
    (ts : ThreadState) (initmem : InitialMem) (mem : PromisingMemory)
    (tid : Fin nThreads) (fuel : Nat)
    : ∀ s ∈ (enumerateResults fuel tid initmem isem termCond ts mem).promises,
        s ∈ (enumerateResults (fuel + 1) tid initmem isem termCond ts mem).promises
 := by
 sorry

theorem promise_select_tid_monotonic_fuel
   : ∀ (pState : ModelState nThreads) (tid : Fin nThreads) (fuel : Nat),
     ∀ s ∈ (promiseSelectTid fuel pState tid isem termCond).oks,
       s ∈ (promiseSelectTid (fuel + 1) pState tid isem termCond).oks
 := by
 sorry

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

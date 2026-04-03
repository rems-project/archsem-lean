import ArchSemTinyArm.Promising
import ArchSem.TerminatingModel

open ArchSemTinyArm.Promising
open ArchSem.TerminatingModel
open ArchSem.NondeterministicMonad


-- TODO: I can probably simplify this by rearranging order of cases.
theorem NExcept.bind_iff {ε α β} (b : β) (m : NExcept ε α) (f : α → NExcept ε β)
     : b ∈ (NExcept.bind m f).oks ↔ ∃ (a : α), a ∈ m.oks ∧ b ∈ (f a).oks
  := by
  apply Iff.intro
  case mp =>
    intro h
    simp [NExcept.bind] at h
    revert h
    induction m.oks
    case nil =>
      intro h
      simp [List.map] at h
    case cons tail ih =>
      rename_i head
      intro mem
      simp [NExcept.merge] at mem
      rcases mem
      case inl =>
        rename_i h
        exact ⟨head, by simp, h⟩
      case inr =>
        rename_i h
        have := ih h
        rcases this with ⟨a, l, r⟩
        exact ⟨a, List.Mem.tail _ l, r⟩
  case mpr =>
    intro h
    simp [NExcept.bind]
    revert h
    induction m.oks
    case nil =>
      intro h
      simp at h
    case cons tail ih =>
      intro h
      rename_i head
      rcases h with ⟨a, h⟩
      rcases h with ⟨left, right⟩
      rcases left
      case head =>
        simp [List.map, NExcept.merge]
        apply Or.inl
        exact right
      case tail inTail =>
        simp [List.map, NExcept.merge]
        apply Or.inr
        apply ih
        exact ⟨a, inTail, right⟩

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

theorem run_to_termination_monotonic_fuel
    (promises : List Msg) (pstate : ProjectedModelState) (tid : Fin nThreads) (initmem : InitialMem) (mem : PromisingMemory)
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
    simp [runToTermination, Bind.bind] at mem
    repeat rw [NEStateM.bind_iff] at mem
    rcases mem with ⟨s', a', h_interp, h⟩
    simp [get, NEStateM.bind, Bind.bind, pure, NExcept.pure, NExcept.bind, NExcept.merge, modify] at h
    split at h
    -- TODO: fix lots of repetition in the cases
    case succ.isFalse =>
      simp [modify, modifyGet, NEStateM.bind, bind, pure, NExcept.pure, NExcept.bind, NExcept.merge] at h
      have := ih s'.fst { threadState := s'.snd.threadState, mem := s'.snd.mem, iis := IIS.init } s h fuelRemains
      rw [runToTermination]
      simp [Bind.bind]
      repeat rw [NEStateM.bind_iff]
      refine ⟨s', a', h_interp, ?_⟩
      simp [get, NEStateM.bind, Bind.bind, pure, NExcept.pure, NExcept.bind, NExcept.merge, modify]
      split
      case isFalse =>
        simp [modifyGet, NEStateM.bind, bind, pure, NExcept.pure, NExcept.bind, NExcept.merge]
        exact this
      case isTrue =>
        contradiction
    case succ.isTrue =>
      rw [runToTermination]
      simp [Bind.bind]
      repeat rw [NEStateM.bind_iff]
      refine ⟨s', a', h_interp, ?_⟩
      simp [get, NEStateM.bind, Bind.bind, pure, NExcept.pure, NExcept.bind, NExcept.merge, modify]
      split
      case isFalse =>
        contradiction
      case isTrue =>
        assumption

theorem enumerate_result_promises_monotonic_fuel
   : ∀ (ts : ThreadState) (initmem : InitialMem) (mem : PromisingMemory)
       (tid : Fin nThreads) (fuel : Nat),
     ∀ s ∈ (enumerateResults fuel tid initmem isem termCond ts mem).promises,
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

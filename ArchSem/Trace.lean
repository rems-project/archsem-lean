-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Sail

/-!
This file defines "Events" and free monad "Traces" over a generic free monad.
These will be used by the axiomatic machinery for reasoning about traces
of instruction effects.
-/

open Sail.ArchSem

namespace ArchSem

/-- An effect paired with a concrete return value. -/
structure FreeM.Event (Eff : Type) [Effect Eff] where
  call : Eff
  ret : Effect.ret call

/-- Notation for constructing an Event. -/
notation:40 call " &→ " ret => {call := call, ret := ret}

namespace FreeM.Event

/-- Extract the return value from an event if the effect matches. -/
def extract [DecidableEq Eff] [Effect Eff]
    (ev : FreeM.Event Eff) (call : Eff) : Option (Effect.ret call) :=
  if h : ev.call = call
  then .some (h ▸ ev.ret)
  else .none

/--
`steps f l f'` holds iff free monad f can generate the trace l and result in the
f' free monad.
-/
inductive steps [Effect Eff]
    : FreeM Eff α → List (FreeM.Event Eff) → FreeM Eff α → Prop
  | nil (f : FreeM Eff α) : steps f [] f
  | cons (call : Eff) (k : Effect.ret call → FreeM Eff α)
      (ret : Effect.ret call) (t : List (FreeM.Event Eff)) (f' : FreeM Eff α)
      : steps (k ret) t f' → steps (.impure call k) ((call &→ ret)::t) f'

theorem steps_nil [Effect Eff] (f f' : FreeM Eff α) : steps f [] f' ↔ f = f' := by
  apply Iff.intro
  · intro h
    cases h
    rfl
  · intro eq
    simp [eq, steps.nil]

/--
A computational version of `FreeM.Event.steps`. Attempt to retrace
the events of l using free monad f and return the resulting free monad.
-/
def replay [DecidableEq Eff] [Effect Eff]
    : FreeM Eff α →  List (FreeM.Event Eff) → Option (FreeM Eff α)
  | f, [] => .some f
  | .impure call k, h::t =>
    match h.extract call with
    | .some r => replay (k r) t
    | .none => .none
  | .pure _, _::_ => .none

theorem replay_some [DecidableEq Eff] [Effect Eff]
    (f f' : FreeM Eff α) (l : List (FreeM.Event Eff))
    : replay f l = .some f' ↔ steps f l f' := by
  apply Iff.intro
  · intro h_replay
    induction f, l using replay.induct
    · simp [replay] at h_replay
      rw [h_replay]
      exact steps.nil f'
    · rename_i call k ev t r h_ex ih
      have {call := call', ret := ret'} := ev
      --simp [extract] at h_ex
      simp [replay, h_ex] at h_replay
      have := ih h_replay
      have := steps.cons call k r t f' this
      rw [extract] at h_ex
      split at h_ex <;> try contradiction
      grind []
    · grind [replay]
    · contradiction
  · intro h_steps
    induction h_steps
    · simp [replay]
    · rename_i k ret t f' a ih
      simp [replay, extract, ih]
    

theorem replay_none [DecidableEq Eff] [Effect Eff]
    (f : FreeM Eff α) (l : List (FreeM.Event Eff))
    : replay f l = .none ↔ ∀ f', ¬(steps f l f') := by
  apply Iff.intro
  · intro h_replay f' h_steps
    have := (replay_some f f' l).mpr h_steps
    rw [h_replay] at this
    contradiction
  · intro h_steps
    cases h_replay : replay f l with
    | none => rfl
    | some f' =>
      have := (replay_some f f' l).mp h_replay
      have := h_steps f'
      contradiction

end FreeM.Event

/-- The end type of a free monad trace. -/
inductive FreeM.Trace.End (Eff α : Type) [Effect Eff] where
  /-- The trace ends in a pure free monad returning `a`. -/
  | ret (a : α)
  /-- The trace ends in a generated effect who's return value is unknown. -/
  | openCall (call : Eff)
  /-- The trace finishes in a resolved state, so any effect can come next. -/
  | stopped

/-- Is the provided free monad compatable with the end type. -/
inductive FreeM.Trace.End.is_end [Effect Eff]
    : FreeM Eff α → FreeM.Trace.End Eff α → Prop
  | ret (a : α) : is_end (.pure a) (.ret a)
  | openCall (call : Eff) (k : Effect.ret call → FreeM Eff α)
      : is_end (.impure call k) (.openCall call)
  | stopped (f : FreeM Eff α) : is_end f .stopped

/-- FreeM.Trace.End.is_end is decidable. -/
instance [DecidableEq α] [DecidableEq Eff] [Effect Eff] (f : FreeM Eff α) (en : FreeM.Trace.End Eff α)
    : Decidable (FreeM.Trace.End.is_end f en) :=
  match f, en with
  | .pure a, .ret a' => by
    if h_eq : a = a' then
      apply Decidable.isTrue
      rw [←h_eq]
      exact FreeM.Trace.End.is_end.ret a
    else
      apply Decidable.isFalse
      intro is_end
      cases is_end
      contradiction
  | .impure call k, .openCall call' => by
    if h_eq : call = call' then
      apply Decidable.isTrue
      rw [←h_eq]
      exact FreeM.Trace.End.is_end.openCall call k
    else
      apply Decidable.isFalse
      intro is_end
      cases is_end
      contradiction
  | f, .stopped => by
    apply Decidable.isTrue
    apply FreeM.Trace.End.is_end.stopped
  | .impure _ _, .ret _
  | .pure _, .openCall _ => by
    apply Decidable.isFalse
    intro h
    nomatch h
  

/--
A trace of a free monad is a description of a possible concrete execution that
does not necessarily go all the way to a terminated `pure` state.
-/
def FreeM.Trace (Eff : Type) [Effect Eff] (α : Type) :=
  List (FreeM.Event Eff) × FreeM.Trace.End Eff α

namespace FreeM.Trace

def ret {Eff α : Type} [Effect Eff] (a : α) : FreeM.Trace Eff α
  := ([], .ret a)
def openCall {Eff α : Type} [Effect Eff] (call : Eff) : FreeM.Trace Eff α
  := ([], .openCall call)
def stopped {Eff α : Type} [Effect Eff] : FreeM.Trace Eff α
  := ([], .stopped)

/-- Prepend an event to a trace -/
def cons [Effect Eff] (ev : FreeM.Event Eff) (tr : FreeM.Trace Eff α)
    : FreeM.Trace Eff α :=
  (ev :: tr.fst, tr.snd)

/-- Is a given free monad capable of generating the provided trace. -/
inductive is_trace [Effect Eff] : FreeM Eff α → FreeM.Trace Eff α → Prop
  | stopped (f : FreeM Eff α) : is_trace f stopped
  | ret (a : α) : is_trace (.pure a) (ret a)
  | openCall (call : Eff) (k : Effect.ret call → FreeM Eff α)
      : is_trace (.impure call k) (openCall call)
  | impure (call : Eff) (k : Effect.ret call → FreeM Eff α) (ret : Effect.ret call)
      (t : FreeM.Trace Eff α)
      : is_trace (k ret) t → is_trace (.impure call k) (cons (call &→ ret) t)

theorem is_trace_steps [Effect Eff] (f : FreeM Eff α) (tr : FreeM.Trace Eff α) :
  is_trace f tr ↔ ∃ f' : FreeM Eff α, FreeM.Event.steps f tr.1 f' ∧ End.is_end f' tr.2
  := by
  apply Iff.intro
  · intro h_tr
    induction h_tr
    case mp.ret a =>
      refine ⟨FreeM.pure a, ?_⟩
      simp [ret, Event.steps.nil, End.is_end.ret]
    case mp.stopped f₀ =>
      refine ⟨f₀, ?_⟩
      simp [stopped, Event.steps.nil, End.is_end.stopped]
    case mp.openCall call k =>
      refine ⟨FreeM.impure call k, ?_⟩
      simp [openCall, Event.steps.nil, End.is_end.openCall]
    case mp.impure call k ret t a ih =>
      rcases ih with ⟨f', ih₁, ih₂⟩
      refine ⟨f', ?_⟩
      constructor
      · constructor
        assumption
      · assumption
  · rintro ⟨f', h_steps, h_end⟩
    rcases tr with ⟨l, en⟩
    simp only [] at h_steps h_end
    induction h_steps
    case mpr.nil f₀ =>
      induction h_end
      case ret a => exact is_trace.ret a
      case openCall call k => exact is_trace.openCall call k
      case stopped f'' => exact is_trace.stopped f''
    case mpr.cons call k ret t f' h_cases ih =>
      exact is_trace.impure call k ret (t, en) (ih h_end)

/-- Determining is_trace is decidable. -/
instance [DecidableEq Eff] [DecidableEq α] [Effect Eff] (f : FreeM Eff α) (tr : FreeM.Trace Eff α)
    : Decidable (is_trace f tr)
  := match h_replay : FreeM.Event.replay f tr.fst with
  | .some f' => by
    have h_steps := (FreeM.Event.replay_some f f' tr.fst).mp h_replay
    if h_end : (End.is_end f' tr.snd)
    then
      apply Decidable.isTrue
      rw [is_trace_steps]
      exact ⟨f', h_steps, h_end⟩
    else
      apply Decidable.isFalse
      rw [is_trace_steps, not_exists]
      intro f''
      rw [← FreeM.Event.replay_some f f'' tr.fst, h_replay]
      rw [not_and]
      intro h_eq
      simp only [Option.some.injEq] at h_eq
      simp [←h_eq, h_end]
  | .none => by
    apply Decidable.isFalse
    rw [is_trace_steps, not_exists]
    intro f'
    rw [and_comm, not_and]
    have h := (FreeM.Event.replay_none f tr.fst).mp h_replay f'
    simp [h]
  
end FreeM.Trace

end ArchSem

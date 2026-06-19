-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Sail
import ArchSem.Defs
import ArchSem.ListSet
import ArchSem.TerminatingModel
import ArchSem.NondeterministicMonad
import ArchSemTinyArm.Defs

open Sail
open Sail.ArchSem
open ArchSem.TerminatingModel
open ArchSem
open ArchSem.NondeterministicMonad

namespace ArchSemTinyArm.Sequential

/-- Sequential model full state. -/
structure SequentialState where
  regs : RegisterMap
  mem : MemoryMap
  /-- Count clock cycle events from the isa semantics. -/
  cycleCount : Nat
  /-- Print messages from the sail isa semantics in reverse order. -/
  sailOutput : List String

/-- Lift architecture-specific state into model-specific state. -/
def SequentialState.ofArchState (archState : ArchState 1) : SequentialState :=
  { regs := archState.regs[0] /- There is only one thread. -/
  , mem := archState.memory
  , cycleCount := 0
  , sailOutput := []
  }

/-- Lower model-specific state into architecture-specific state. -/
def SequentialState.toArchState (state : SequentialState) : ArchState 1 :=
  { regs := ⟨#[state.regs], rfl⟩
  , memory := state.mem
  , addressSpace := default
  }

/-- Decidable proposition that a model state has terminated under the condition. -/
def SequentialState.has_terminated (termCond : TerminationCondition 1)
    (state : SequentialState) : Prop :=
  state.toArchState.has_terminated termCond
deriving Decidable

/-- Interpret an ISA effect into a sequential state non-deterministic monad. -/
def interpretEffect : (eff : InstructionEffect) → NEStateM String SequentialState (eff.ret)
  | .regRead reg racc => do
    match racc with | none => pure () | some _ => Except.error "Non trivial reg access types unsupported"
    match (← get).regs.get? reg with
    | .some s => pure s
    | .none => Except.error s!"Cant read unmapped register: {reprStr reg}"
  | .regWrite reg racc value => do
    match racc with | none => pure () | some _ => Except.error "Non trivial reg access types unsupported"
    modify (fun s => { s with regs := s.regs.insert reg value })
  | .memRead req => do
    if req.numTag != 0 then Except.error "Memory request tags not supported"
    let addr := req.address.toNat
    let value := (← get).mem.read req.size addr
    pure (.ok (value, BitVec.zero 0))
  | .memWriteAnnounce _memReq => pure ()
  | .memWrite req value _tags => do
    let mem := (← get).mem.write req.size req.address value
    modify (fun s => { s with mem := mem})
    pure (.ok ())
  | .barrier _barrier => pure ()
  | .clockCycle => modify (fun s => { s with cycleCount := s.cycleCount + 1 })
  | .getCycleCount => do pure (← get).cycleCount
  | .archException exception =>
    Except.error s!"Architecture exception: {reprStr exception}"
  | .printMessage msg => modify fun s ↦ { s with sailOutput := msg :: s.sailOutput }
  | .cacheOp _op
  | .tlbOp _op
  | .translationStart _translationStart
  | .translationEnd _translationEnd
  | .returnExecption => Except.error "Unsupported effect"

/-- Interpret the given instruction semantics into the sequential models monad. -/
def sequentialInterpreter : SailM Unit → NEStateM String SequentialState Unit :=
  FreeM.liftM (fun
    | .inl (.error err) => Except.error err.print
    | .inl (.ok eff) => interpretEffect eff
    | .inr choice => NEStateM.chooseFin choice)

/-- A model state paired with a proof of its termination under the given condition. -/
structure TerminatedSequentialState (termCond : TerminationCondition 1) where
  state : SequentialState
  proof : state.has_terminated termCond

/--
Run the instruction semantics until the fuel runs out or the termination
condition is reached.
-/
def runToTermination (fuel : Nat) (isem : SailM Unit) (termination : TerminationCondition 1)
    : NEStateM String SequentialState (TerminatedSequentialState termination) :=
  match fuel with
  | 0 => Except.error "out of fuel"
  | fuel + 1 => do
    sequentialInterpreter isem
    let st ← get
    if h : st.has_terminated termination then
      return { state := st, proof := h }
    else
      runToTermination fuel isem termination

/-- Create an abstract `ComputationalTerminatingModel` for our sequential model. -/
def createSequentialModel (isem : SailM Unit) (fuel : Nat) : ComputationalTerminatingModel
  | 1, (termCond : TerminationCondition 1), (initialState : ArchState 1) =>
    let seqState : SequentialState := SequentialState.ofArchState initialState
    let results := runToTermination fuel isem termCond seqState
    let errors : ListSet String := results.errors.map Prod.snd
    let finalStates : ListSet (TerminatedSequentialState termCond) := results.oks.map Prod.snd
    let terminatedToFinalState (terminated : TerminatedSequentialState termCond)
        : ModelResult 1 Unit termCond :=
      ModelResult.finalState terminated.state.toArchState terminated.proof
    (errors.map ModelResult.error).union (finalStates.map terminatedToFinalState)
  | nThreads, _termCond, _initialState =>
    ListSet.ofList [ModelResult.error
      s!"Sequential model only supports one thread, not {nThreads}."]

end ArchSemTinyArm.Sequential

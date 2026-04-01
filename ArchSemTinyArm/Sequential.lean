import Sail
import ArchSem.Common
import ArchSem.TerminatingModel
import ArchSem.NondeterministicMonad
import ArchSemTinyArm.Defs

open Sail
open Sail.ArchSem
open ArchSem.TerminatingModel
open ArchSem.NondeterministicMonad

namespace ArchSemTinyArm.Sequential

structure SequentialState where
  regs : RegisterMap
  mem : MemoryMap
  cycleCount : Nat
  sailOutput : List String

def SequentialState.ofArchState (archState : ArchState 1) : SequentialState :=
  { regs := archState.regs[0]
  , mem := archState.memory
  , cycleCount := 0
  , sailOutput := []
  }

def SequentialState.toArchState (state : SequentialState) : ArchState 1 :=
  { regs := ⟨#[state.regs], rfl⟩
  , memory := state.mem
  , addressSpace := default
  }

def SequentialState.has_terminated (termCond : TerminationCondition 1)
    (state : SequentialState) : Prop :=
  state.toArchState.has_terminated termCond
deriving Decidable

--instance : Decidable (SequentialState.has_terminated termCond state) :=
--  state.toArchState.has_terminated termCond

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
  | .choice n => NEStateM.chooseFin n
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

def sequentialInterpreter : SailM Unit → NEStateM String SequentialState Unit
  | .pure () => pure ()
  | .impure (.error err) _cont => Except.error err.print
  | .impure (.ok eff) cont => do
    let x ← interpretEffect eff
    sequentialInterpreter (cont x)

structure TerminatedSequentialState (termCond : TerminationCondition 1) where
  state : SequentialState
  proof : state.has_terminated termCond

def runToTermination (fuel : Nat) (isem : SailM Unit) (termination : TerminationCondition 1)
    : NEStateM String SequentialState (TerminatedSequentialState termination) :=
  match fuel with
  | 0 => Except.error "out of fuel"
  | fuel+1 => do
    sequentialInterpreter isem
    let st ← get
    if h : st.has_terminated termination then
      return { state := st, proof := h }
    else
      runToTermination fuel isem termination

def createSequentialModel (isem : SailM Unit) (fuel : Nat) : ComputationalTerminatingModel
  | 1, (termCond : TerminationCondition 1), (initialState : ArchState 1) =>
    let seqState : SequentialState := SequentialState.ofArchState initialState
    let results := runToTermination fuel isem termCond seqState
    let errors : List String := results.errors.map Prod.snd
    let finalStates : List (TerminatedSequentialState termCond) := results.oks.map Prod.snd
    let terminatedToFinalState (terminated : TerminatedSequentialState termCond)
        : ModelResult 1 Unit termCond :=
      ModelResult.finalState terminated.state.toArchState terminated.proof
    (errors.map ModelResult.error) ++ (finalStates.map terminatedToFinalState).eraseDups
  | nThreads, _termCond, _initialState =>
    [ModelResult.error s!"Sequential model only supports one thread, not {nThreads}."]

end ArchSemTinyArm.Sequential

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap
import Sail
import Out.Defs
import ArchsemLean.Common

open Sail
open Sail.ArchSem

namespace ArchSem.Sequential

structure ChoiceSource where
  (α : Type)
  (nextState : Nat → α → α)
  (choose : (n : Nat) → [NeZero n] → α → Fin n)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose _ _ _ := 0

structure SequentialState (c : ChoiceSource) where
  regs : RegisterMap
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat
  sailOutput : Array String -- TODO: be able to use an IO monad to run

def readByte (addr : Nat)
    : EStateM (Error ue) (SequentialState c) (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

def writeByte (addr : Nat) (value : BitVec 8)
    : EStateM (Error ue) (SequentialState c) PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }

def readBytes (size : Nat) (addr : Nat)
    : EStateM (Error ue) (SequentialState c) (BitVec (8 * size)) :=
  match size with
  | 0 => pure BitVec.nil
  | 1 => do
    let b ← readByte addr
    have h : 8 * 1 = 8 := rfl
    return (h ▸ b)
  | n + 1 => do
    let b ← readByte addr
    let bytes ← readBytes n (addr+1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return (h ▸ bytes.append b)

def writeBytes (addr : Nat) (value : BitVec (8 * size))
    : EStateM (Error ue) (SequentialState c) PUnit :=
  let list := List.ofFn (fun i : Fin size => (addr + i.val, value.extractLsb' (i.val * 8 + 8) 8))
  List.forM list (fun (a, v) => writeByte a v)

def interpretEffect : (eff : InstructionEffect) → EStateM (Error userError) (SequentialState c) (eff.ret)
  | .regRead reg _accessType => do
    let .some s := (← get).regs.get? reg
      | throw .Unreachable
    pure s
  | .regWrite reg _accessType value =>
    modify fun s => { s with regs := s.regs.insert reg value }
  | .memRead req => do
    let addr := req.address.toNat
    let value ← readBytes req.size addr
    .pure (.Ok (value, BitVec.zero req.size))
  | .memWrite req value _tags => do
    let addr := req.address.toNat
    writeBytes addr value
    pure (Ok ())
  | .memWriteAnnounce _memReq => .pure ()
  | .barrier _barrier => .pure ()
  | .cacheOp _op => .pure ()
  | .tlbOp _op => .pure ()
  | .choice 0 => throw (.Assertion
    "This sequential memory model does not support backtracking nondeterminisim. \
     Use a smarter memory consistency model or a dumber ISA model.")
  | .choice (n+1) =>
    modifyGet (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState n σ.choiceState }))
  | .clockCycle => modify fun s => { s with cycleCount := s.cycleCount + 1 }
  | .getCycleCount => do pure (← get).cycleCount
  | .translationStart _translationStart => .pure ()
  | .translationEnd _translationEnd => .pure ()
  | .archException _exception => .pure ()
  | .returnExecption => .pure ()
  | .printMessage msg => modify fun s ↦ { s with sailOutput := s.sailOutput.push msg }
  

def sequentialInterpreter : PreSailM userError Unit → EStateM (Error userError) (SequentialState c) Unit
  | .pure () => .pure ()
  | .impure (.Err err) _cont => EStateM.throw err
  | .impure (.Ok eff) cont => EStateM.bind (interpretEffect eff) (fun r => sequentialInterpreter (cont r))

def main_of_sail_main (initialState : SequentialState c) (main : Unit → PreSailM ue Unit) : IO UInt32 := do
  let stateM := sequentialInterpreter (main ())
  let res := stateM.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

def sequentialModel (fuel : Nat) (isem : PreSailM userError Unit) (termination : TerminationCondition 1)
    : EStateM (Error userError) (SequentialState c) Unit :=
  match fuel with
  /- CR clang: out-of-fuel should not be an assertion error. Think about this. -/
  | 0 => throw (.Assertion "out of fuel")
  | fuel+1 => do
    sequentialInterpreter isem
    let st ← get
    match termination 0 st.regs with
    | true => return ()
    | false => sequentialModel fuel isem termination

end ArchSem.Sequential

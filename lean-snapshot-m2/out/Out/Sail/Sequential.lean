import Out.Sail.Sail

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

open Sail
open PreSail
open ArchSem

structure ChoiceSource where
  (α : Type)
  (nextState : Primitive → α → α)
  (choose : ∀ p : Primitive, α → p.reflect)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

variable [Arch] [DecidableEq Arch.register] [Hashable Arch.register]

structure SequentialState (c : ChoiceSource) where
  regs : Std.ExtDHashMap Arch.register Arch.register_type
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run

def readByte (addr : Nat) : EStateM (Error ue) (SequentialState c) (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

def writeByte (addr : Nat) (value : BitVec 8) : EStateM (Error ue) (SequentialState c) PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }

def interpretEffect : (eff : InstructionEffect) → EStateM (Error userError) (SequentialState c) (eff.ret)
  | .regRead reg _accessType => do
    let .some s := (← get).regs.get? reg
      | throw .Unreachable
    pure s
  | .regWrite reg _accessType value =>
    modify fun s => { s with regs := s.regs.insert reg value }
    /- CR clang: the current sail-lean read bytes state monad implementation is really weird. -/
    /- CR clang: check I'm doing the right edianness here... -/
  | .memRead req => do
    let addr := req.address.toNat
    let list ← List.ofFnM (m := EStateM (Error userError) (SequentialState c))
      (fun i : Fin req.size => readByte (addr + i.val))
    .pure (.Ok (List.foldl (fun acc b => BitVec.append acc b) (BitVec.zero 0) list, BitVec.zero req.size))
  | .memWrite req value _tags => do
    let addr := req.address.toNat
    let list := List.ofFn (fun i : Fin req.size => (addr + i.val, value.extractLsb' (i.val * 8 + 8) 8))
    List.forM list (fun (a, v) => writeByte a v)
    pure (Ok ())
  | .memWriteAnnounce _memReq => .pure ()
  | .barrier _barrier => .pure ()
  | .cacheOp _op => .pure ()
  | .tlbOp _op => .pure ()
  | .choice primitive =>
    modifyGet (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState primitive σ.choiceState }))
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


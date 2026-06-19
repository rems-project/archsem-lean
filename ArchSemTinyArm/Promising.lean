-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.Defs
import ArchSem.NondeterministicMonad
import ArchSem.TerminatingModel
import ArchSemTinyArm.Defs

/-!
This module contains a handwritten lean port of ArchSem rocq's
ArchSemArm/UMPromising.v at 6f2c001d9f1294c4c3ee41c92ab5e630cad867e7
Febuary 2026.
Which in turn is heavily based upon
[the PDL19 promising paper](https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf).
Many of the variable naming conventions I take from the paper.

The goal of this module is to define an User-mode promising model without
mixed-size on top of the ArchSem lean interface.
-/

open Sail.ArchSem
open ArchSem.NondeterministicMonad
open ArchSem.TerminatingModel
open ArchSem

namespace ArchSemTinyArm.Promising

/--
This model only works for 8-bytes aligned location, as there in no support for
mixed-sizes yet.
To get the 64-bit physical address, left shift by 3 bits.
-/
abbrev Loc := BitVec 61

/-- Recover a location from an ARM physical address. Return none if unaligned. -/
def Loc.fromAddr (addr : BitVec 64) : Option Loc :=
  if BitVec.extractLsb 2 0 addr == BitVec.zero 3 then
    .some (BitVec.extractLsb 63 3 addr)
  else .none /- unaligned -/

/-- Convert a aligned loc to an ARM physical address. -/
def Loc.toAddr (loc : Loc) : BitVec 64 :=
  BitVec.append loc (BitVec.zero 3)

/-- Register and memory values (all memory access are 8 bytes aligned). -/
abbrev Value := BitVec 64

/-- Timestamps index (reversed) into the `PromisingMemory`. -/
abbrev Timestamp := Nat

/-- A view records a timeatamp of a memory write to capture some ordering requirement. -/
abbrev View := Timestamp

/--
This is an message (recording a write) in the promising model memory.
The location is an aligned physical address as virtual memory is ignored
by this model.
-/
structure Msg where
  /-- Origin thread id of the write. -/
  tid : Tid
  loc : Loc
  val : Value
deriving DecidableEq, Repr

/--
Memory is an extensional tree map.
Unlike the standard hash maps, this gives us both decidable equality
and the ability to enumerate (key,value) pairs.
-/
def InitialMem := Std.ExtTreeMap Loc Value
def InitialMem.empty : InitialMem := Std.ExtTreeMap.empty

/-- Read from an 8-byte aligned location. -/
def InitialMem.read (init : InitialMem) (loc : Loc) : Option Value := init.get? loc

/-- Convert a model-generic `MemoryMap` into the promising models `InitialMem`. -/
def InitialMem.ofMemoryMap (mem : MemoryMap) : InitialMem :=
  let insertByte (init : InitialMem) (pair : BitVec 64 × BitVec 8) : InitialMem :=
    let (addr, value) := pair
    let lowerBits : BitVec 3 := addr.truncate 3
    let loc : Loc := addr.extractLsb 63 3
    let word := init.getD loc (BitVec.zero 64)
    let newWord := BitVec.or word ((value.zeroExtend 64) <<< (8 * lowerBits.toNat))
    init.insert loc newWord
  mem.toList.foldl insertByte InitialMem.empty

/--
The promising memory is a list of messages (write events) in
reverse chronological order.
We index the `PromisingMemory` with `Timestamp`s, where timestap `0`
refers to the `InitialMem`; timestamp `1` refers to the right-most (oldest)
element in the list and so on going from right-to-left through the list.
-/
abbrev PromisingMemory := List Msg

namespace PromisingMemory

/-- Get the unique message (write event) associated with the timestamp if it exists. -/
def lookup (t : Timestamp) (mem : PromisingMemory) : Option Msg :=
  if t == 0 then .none
  else if t <= mem.length then mem[mem.length - t]?
  else .none

/--
Cuts the memory to only what exists before the timestamp, inclusive.
The timestamp can still be computed the same way.
-/
def cutBefore (t : Timestamp) (mem : PromisingMemory) : PromisingMemory :=
  /- Here I'm using the m - n = 0 when n > m behavior -/
  List.drop (mem.length - t) mem

/--
Cuts the memory to only what exists after the timestamp (exclusive).
Beware of timestamp computation. If you need the original timestamps,
use cutAfterWithTimestamps.
-/
def cutAfter (t : Timestamp) (mem : PromisingMemory) : PromisingMemory :=
  List.take (mem.length - t) mem

/-- Return a copy of the promising memory with timestamps attached to write events. -/
def attachTimestamps (mem : PromisingMemory) : List (Msg × Timestamp) :=
  match mem with
  | [] => []
  | h :: t => (h, List.length mem) :: attachTimestamps t

/--
Cuts the memory to only what exists after the timestamp (exclusive)
and attach the original timestamps to each write message.
-/
def cutAfterWithTimestamps (t : Timestamp) (mem : PromisingMemory) : List (Msg × Timestamp) :=
  List.take (mem.length - t) (mem.attachTimestamps)

/--
Produce a memory map by applying all writes in order from a promising memory
onto an initial memory.
-/
def toMemoryMap (init : InitialMem) (mem : PromisingMemory) : MemoryMap :=
  let latest : Std.ExtTreeMap Loc (BitVec (8*8)) :=
    mem.foldr (fun msg m => m.insert msg.loc msg.val) init
  latest.foldl (fun m loc value => m.write 8 (Loc.toAddr loc) value) MemoryMap.empty

end PromisingMemory

/--
Forwarding item to be used in a `ThreadState`s forwarding bank.
A forwarding item records information about a threads last write to a location.
-/
structure FwdItem where
  /-- The timestamp of the write. -/
  time : Timestamp
  /-- The max view of the writes dependencies. -/
  view : View
  /-- Marks if the write was exclusive. -/
  xcl : Bool
deriving Hashable

def FwdItem.init : FwdItem := { time := 0, view := 0, xcl := false }

instance : Hashable (Sigma (fun reg : Arch.register => (Arch.register_type reg) × View)) where
  hash v := hash (v.1, v.2.1, v.2.2)

/-- A single threads inter-instruction state according to the model. -/
structure ThreadState where
  /--
  The promises that this thread must fullfil.
  Is must be ordered with oldest promises at the back of the list.
  -/
  promises : List Timestamp
  /--
  The threads registers and TODO: explain the view attached to register.
  `regs` is a tree map for the same reason MemoryMap is.
  -/
  regs : Std.ExtDTreeMap Arch.register (fun reg => (Arch.register_type reg) × View)
  /-- The coherence views. The max view of all reads and writes from this location. -/
  coh : Std.ExtTreeMap Loc View

  /-- The maximum output view of a read. -/
  vrd : View
  /-- The maximum output view of a write. -/
  vwr : View
  /-- The maximum output view of a dmb st. -/
  vdmbst : View
  /-- The maximum output view of a dmb ld or dmb sy. -/
  vdmb : View
  /-- The maximum output view of control or address dependency. -/
  vcap : View
  /-- The maximum output view of an isb. -/
  visb : View
  /-- The maximum output view of an acquire access. -/
  vacq : View
  /-- The maximum output view of an release access. -/
  vrel : View

  /-- Forwarding bank. Stores records about the last write to each location by this thread. -/
  fwdb : Std.ExtTreeMap Loc FwdItem

  /--
  Exclusives bank. If there was a recent load exclusive but the corresponding
  store exclusive has not yet run, this will contain the timestamp and post-view
  of the load exclusive
  -/
  xclb : Option (Timestamp × View)
deriving Hashable

/--
Reads the last write to a location in some memory. Gives the value and the
timestamp of the write that it read from. The timestamp is 0 iff reading from
initial memory.
-/
def readLast (loc : Loc) (init : InitialMem) (mem : PromisingMemory) : Option (Value × Timestamp) :=
  match mem with
  | [] => Option.map (·, 0) (init.read loc)
  | msg :: mem' =>
    if msg.loc == loc then
      .some (msg.val, mem.length)
    else readLast loc init mem'

/--
Reads from initial memory or fail if the memory has since been overwritten.
This is mainly for instruction fetching.
-/
def readInitial (loc : Loc) (init : InitialMem) (mem : PromisingMemory) : Option Value :=
  match readLast loc init mem with
  | .some (x, 0) => .some x
  | _ => .none

/--
Returns the list of possible reads at a location restricted by a certain view.
The list is never empty as one can always read from at least the initial value.
Returns none if the address is not mapped in initial memory
-/
def read (loc : Loc) (v : View) (init : InitialMem) (mem : PromisingMemory)
    : Option (ListSet (Value × Timestamp)) :=
  match mem.cutBefore v |> readLast loc init with
  | .none => .none /- `loc` not mapped in initial memory -/
  | .some first =>
    let lasts := mem.cutAfterWithTimestamps v
              |> List.filter (fun (msg, _) => msg.loc == loc)
              |> List.map (fun (msg, v) => (msg.val, v))
    .some (ListSet.ofList (lasts ++ [first]))

/--
Returns a view among a promise set that correspond to a message. The oldest
matching view is taken. This is because it can be proven that taking a more
recent view, will make the previous promises unfulfillable and thus the
corresponding executions would be discarded. TODO prove it.
-/
def fulfill (msg : Msg) (prom : List Timestamp) (mem : PromisingMemory) : Option View :=
  prom.filter (fun t => mem.lookup t == .some msg)
    |> List.reverse
    |> List.head?

/--
Check that the write at the provided timestamp is indeed to that location
and that no write to that location have been made by any other thread.
-/
def exclusive (loc : Loc) (t : Timestamp) (mem : PromisingMemory) : Bool :=
  match mem.lookup t with
  | .none => false
  | .some msg =>
    msg.loc == loc &&
    (mem.cutAfter t).all (fun msg' => (msg'.tid == msg.tid) || !(msg'.loc == msg.loc))

def ThreadState.init (regs : RegisterMap) : ThreadState :=
  { promises := []
  , regs := regs.map (fun _r rv => (rv, 0))
  , coh := default
  , vrd := 0
  , vwr := 0
  , vdmbst := 0
  , vdmb := 0
  , vcap := 0
  , visb := 0
  , vacq := 0
  , vrel := 0
  , fwdb := default
  , xclb := .none
  }

/--
Extract a plain register map from the thread state without views.
This is used to decide if a thread has terminated and to observe
the results of the model.
-/
def ThreadState.regMap (ts : ThreadState) : RegisterMap :=
  ts.regs.map (fun _r (rv,_) => rv)

/-- Update the value of reg if it has been initialized. -/
def ThreadState.setReg (reg : Arch.register) (rv : (Arch.register_type reg) × View) (ts : ThreadState)
    : Option ThreadState :=
  if ts.regs.contains reg then
    .some { ts with regs := ts.regs.insert reg rv }
  else
    .none

def ThreadState.setCoherenceView (loc : Loc) (v : View) (ts : ThreadState) : ThreadState :=
  { ts with coh := ts.coh.insert loc v }

def ThreadState.updateCoherenceView (loc : Loc) (v : View) (ts : ThreadState) : ThreadState :=
  ts.setCoherenceView loc (max v (ts.coh.getD loc 0))

def ThreadState.setForwardingItem (loc : Loc) (fi : FwdItem) (ts : ThreadState) : ThreadState :=
  { ts with fwdb := ts.fwdb.insert loc fi }

/-- Promise that this thread will eventually fulfill the memory event with timestamp `t`. -/
def ThreadState.promise (t : Timestamp) (ts : ThreadState) : ThreadState :=
  { ts with promises := t :: ts.promises }


section InstructionSemantics

def viewIf (b : Bool) (v : View) : View := if b then v else 0

/-- The view of a read from a forwarded write. -/
def readFwdView (macc : Arch.mem_acc) (f : FwdItem) : View :=
  if f.xcl && (Arch.mem_acc_is_rel_acq macc) then f.time else f.view

/--
Performs a memory read at a location with a view and return possible output
states with the timestamp and value of the read.
-/
def readMem (loc : Loc) (vaddr : View) (macc : Arch.mem_acc)
    (init : InitialMem) (mem : PromisingMemory)
    : NEStateM String ThreadState (Timestamp × Value) := do
  if Arch.mem_acc_is_atomic_rmw macc then Except.error "Atomic RMW unsupported"
  let ts ← get
  let vbob := max ts.vdmb ts.visb |>.max ts.vacq
    |>.max (viewIf (Arch.mem_acc_is_rel_acq_rcsc macc) ts.vrel)
  let vpre := max vaddr vbob
  let vread := max vpre (ts.coh.getD loc 0)
  let reads ← match read loc vread init mem with
  | .none => Except.error "Reading from unmapped memory"
  | .some reads => pure reads
  let (res, time) ← NEStateM.choose reads
  let read_view :=
    match ts.fwdb.get? loc with
    | some fwd => if fwd.time == time then readFwdView macc fwd else time
    | none => time
  let vpost := max vpre read_view
  modify (ThreadState.updateCoherenceView loc time)
  modify ({· with vrd := max ts.vrd vpost})
  modify ({· with vacq := max ts.vacq (viewIf (Arch.mem_acc_is_rel_acq macc) vpost)})
  modify ({· with vcap := max ts.vcap vaddr})
  if Arch.mem_acc_is_exclusive macc then
    modify ({· with xclb := (time, vpost)})
  return (vpost, res)

-- TODO: clean up write functions and explain return values.
/--
Performs a memory write for a thread tid at a location loc with view
vaddr and vdata. Return the new state.

This may mutate memory if no existing promise can be fullfilled.
-/
def writeMem (tid : Nat) (loc : Loc) (vdata : View)
    (macc : Arch.mem_acc) (mem : PromisingMemory) (data : Value)
    : NEStateM String ThreadState (PromisingMemory × View × Option View) := do
  let msg := { tid, loc, val := data }
  let is_release := Arch.mem_acc_is_rel_acq macc
  let ts ← get
  let (time, mem, new_promise) :=
    match fulfill msg ts.promises mem with
    | some t => (t, mem, false)
    | none =>
      let newMem := msg :: mem
      let view := newMem.length
      (view, newMem, true)
  let vbob :=
    max ts.vdmbst ts.vdmb |>.max ts.visb |>.max ts.vacq
    |>.max (viewIf is_release (max ts.vrd ts.vwr))
  let vpre := max vdata ts.vcap |>.max vbob
  if (max vpre (ts.coh.getD loc 0)) >= time then
    NEStateM.discard
  modify (fun ts => { ts with promises := ts.promises.filter (· != time) })
  modify (fun ts => ts.updateCoherenceView loc time)
  modify ({· with vwr := max ts.vwr time})
  modify ({· with vrel := max ts.vrel (viewIf is_release time)})
  pure (mem, time, (if new_promise then some vpre else none))

/-- Perform a memory write (that may or may not be exclusive). -/
def writeMemXcl (tid : Nat) (loc : Loc)
    (vdata : View) (macc : Arch.mem_acc)
    (mem : PromisingMemory) (data : Value)
    : NEStateM String ThreadState (PromisingMemory × Option View) := do
  if Arch.mem_acc_is_atomic_rmw macc then Except.error "Atomic RMW unsupported" else
  let xcl := Arch.mem_acc_is_exclusive macc
  if xcl then
    let (mem, time, vpreOpt) ← writeMem tid loc vdata macc mem data
    let ts ← get
    match ts.xclb with
    | none => NEStateM.discard
    | some (xtime, _xview) =>
      if !(exclusive loc xtime (mem.cutAfter time)) then
        NEStateM.discard
    modify (ThreadState.setForwardingItem loc { time, view := vdata, xcl := true })
    modify (fun ts => {ts with xclb := none})
    return (mem, vpreOpt)
  else
    let (mem, time, vpreOpt) ← writeMem tid loc vdata macc mem data
    modify (ThreadState.setForwardingItem loc { time, view := vdata, xcl := false })
    return (mem, vpreOpt)


/--
The inter-instruction (multiple threads) state of the model.
In archsem-rocq its called PState (Promising State)
-/
structure ModelState (nThreads : Nat) where
  threadStates : Vector ThreadState nThreads
  initmem : InitialMem
  mem : PromisingMemory

/-- Convert model-specific `ModelState` to architecture-wide, model-generic `ArchState`. -/
def ModelState.toArchState (mState : ModelState nThreads) : ArchState nThreads :=
  { memory := mState.mem.toMemoryMap mState.initmem
  , addressSpace := ()
  , regs := mState.threadStates.map (fun tstate => tstate.regMap)
  }

/-- Intra-Instruction State for propagating views inside an instruction. -/
structure IIS where
  strict : View

/-- The intra-instruction state at the begining of an instruction. -/
def IIS.init : IIS := { strict := 0 }
def IIS.add (v : View) (iis : IIS) : IIS :=
  { iis with strict := iis.strict.max v }


/--
The ModelState projected onto a single thread so that it can be used in state
monads which only concern one thread.
In archsem-rocq this is called PPState (Partial Promising State).
-/
structure ProjectedModelState where
  threadState : ThreadState
  mem : PromisingMemory
  iis : IIS

/- Conversion between ModelState and ProjectedModelState. -/
def projectModelState (tid : Fin n) (mstate : ModelState n) : ProjectedModelState :=
  { threadState := mstate.threadStates[tid], mem := mstate.mem, iis := IIS.init }
def injectModelState (tid : Fin n) (pmstate : ProjectedModelState) (mstate : ModelState n) : ModelState n :=
  { mstate with threadStates := mstate.threadStates.set tid pmstate.threadState, mem := pmstate.mem }

/-- Automatically lift a thread state moand into a projected model state monad. -/
instance : MonadLift (NEStateM ε ThreadState) (NEStateM ε ProjectedModelState) where
  monadLift := NEStateM.liftStateFull ProjectedModelState.threadState
   (fun tstate pmstate => { pmstate with threadState := tstate })

/--
Runs an effect in the promising model while doing the correct view tracking and
computation. This can mutate memory because it will append a write at the end of
memory the corresponding event was not already promised.
-/
def runEffect (tid : Nat) (initmem : InitialMem) (eff : InstructionEffect)
    : NEStateM String ProjectedModelState ((InstructionEffect.ret eff) × Option View) :=
  match eff with
  | .regWrite reg racc val => do
    match racc with | none => pure () | some _ => Except.error "Non trivial reg access types unsupported"
    let vreg := (← get).iis.strict
    let vreg' ←
      if reg == ._PC then
        modify (fun ps => { ps with threadState := {ps.threadState with vcap := max ps.threadState.vcap vreg} })
        pure 0
      else pure vreg
    let ts := (← get).threadState
    let nts ← match ts.setReg reg (val, vreg') with
      | .none => Except.error "Register isn't mapped, can't write"
      | .some nts => pure nts
    modify (fun s => { s with threadState := nts })
    return ((), none)
  | .regRead reg racc => do
    match racc with | none => pure () | some _ => Except.error "Non trivial reg access types unsupported"
    let ts := (← get).threadState
    let (val, view) ← match ts.regs.get? reg with
      | .none => Except.error "Register isn't mapped can't read"
      | .some x => pure x
    modify (fun ps => { ps with iis := ps.iis.add view })
    return (val, none)
  | .memRead memReq => do
    if memReq.numTag != 0 then Except.error "Memory request tags not supported"
    match memReq.size with
    | 4 => /- ifetch -/
      /-
      In this model, we assume all memory accesses are 8 byte aligned, with the sole exception
      being instruction fetches which are always 4 bytes and must be from initial memory.
      -/
      if !Arch.mem_acc_is_ifetch memReq.accessKind then Except.error "Non-ifetch 4 bytes access" else
      let addr : BitVec 64 := memReq.address
      /- Extract bit-2 to align the 4-byte read to 8-bytes. -/
      let bit2 := addr.getLsb 2
      let aligned_addr := BitVec.and addr (BitVec.ofNat 64 0b100).not
      /- The 8-byte aligned location containing the 4-bytes to be read. -/
      let loc ← match Loc.fromAddr aligned_addr with
      | .none => Except.error s!"Ifetch must be 4-byte aligned {addr}"
      | .some loc => pure loc
      let word ← match readInitial loc initmem (← get).mem with
      | .none => Except.error s!"Modified instruction memory at {loc} {aligned_addr}"
      | .some word => pure word
      let opcode : BitVec 32 := (if bit2 then word.extractLsb 63 32 else word.extractLsb 31 0)
      return (.ok (opcode, BitVec.zero 0), none)
    | 8 =>
      let loc ← match Loc.fromAddr memReq.address with
        | .none => Except.error s!"Address not supported {memReq.address}"
        | .some loc => pure loc
      if Arch.mem_acc_is_ifetch memReq.accessKind then Except.error "i-fetch must be 4 byte" else
      if !Arch.mem_acc_is_explicit memReq.accessKind then Except.error "read must be explicit" else
      let vaddr := (← get).iis.strict
      let mem := (← get).mem
      let (view, val) ← readMem loc vaddr memReq.accessKind initmem mem
      modify (fun s => { s with iis := s.iis.add view })
      return (.ok (val, BitVec.zero 0), none)
    | _ => Except.error "Memory read of size other than 8 and 4"
  | .memWriteAnnounce _ => do
    let vaddr := (← get).iis.strict
    modify (fun ps => { ps with threadState := {ps.threadState with vcap := max ps.threadState.vcap vaddr} })
    return ((), none)
  | .memWrite memReq val _tags => do
    match memReq.size with
    | 8 =>
      let loc ← match Loc.fromAddr memReq.address with
        | .none => Except.error "Address not supported"
        | .some loc => pure loc
      if !Arch.mem_acc_is_explicit memReq.accessKind then Except.error "Unsupported non-explicit write" else
      let mem := (← get).mem
      let vdata := (← get).iis.strict
      let (mem, vpreOpt) ← writeMemXcl tid loc vdata memReq.accessKind mem val
      modify (fun s => {s with mem := mem})
      return (.ok (), vpreOpt)
    | _ => Except.error "Unsupported memory write size"
  | .barrier (Barrier.Barrier_DMB dmb) => do
    let ts := (← get).threadState
    match dmb.types with
    | .MBReqTypes_All =>
      modify ({ · with threadState := {ts with vdmb := max ts.vdmb (max ts.vrd ts.vwr)} })
    | .MBReqTypes_Reads =>
      modify ({ · with threadState := {ts with vdmb := max ts.vdmb ts.vrd} })
    | .MBReqTypes_Writes =>
      modify ({ · with threadState := {ts with vdmbst := max ts.vdmbst ts.vwr} })
    return ((), none)
  | .barrier (Barrier.Barrier_ISB ()) => do
    let ts := (← get).threadState
    modify ({ · with threadState := {ts with visb := max ts.visb ts.vcap} })
    return ((), none)
  | .barrier b => Except.error s!"Unsupported barrier: {reprStr b}"
  | .archException exception =>
    Except.error s!"Architecture exception: {reprStr exception}"
  | .printMessage msg =>
    Except.error s!"Message printing currently unsupported: '{msg}'"
  | .cacheOp _op
  | .tlbOp _op
  | .clockCycle
  | .getCycleCount
  | .translationStart _translationStart
  | .translationEnd _translationEnd
  | .returnExecption => Except.error s!"Unsupported effect"

end InstructionSemantics

section ModelEvaluation

/--
Check if a specific thread has terminated according to the termination condition.
-/
def threadTerminated
    (termination : TerminationCondition n)
    (mstate : ModelState n)
    (tid : Fin n) : Bool :=
  termination tid mstate.threadStates[tid].regMap

/--
A proof that all threads have terminated according to the termination condition.
-/
def all_threads_terminated
    (termination : TerminationCondition n)
    (mstate : ModelState n) : Prop :=
  ∀ tid : Fin n, threadTerminated termination mstate tid
deriving Decidable

/--
Given a proof that the promising model state (ModelState) is terminated,
we can construct a proof that the corresponding architecture state
(ArchState) is terminated according to the same termination condition.
-/
theorem terminated_model_state_to_arch_state
    : all_threads_terminated termination mstate
    → ArchState.has_terminated termination mstate.toArchState := by
  simp [all_threads_terminated, ArchState.has_terminated, ModelState.toArchState, threadTerminated]

/-- Return true iff there are no outstanding promises in all threads. -/
def noPromises (mstate : ModelState n) : Bool :=
  mstate.threadStates.all (fun tstate => tstate.promises.isEmpty)

/--
Use an instruction effect handler to interpret the instruction semantics monad
into a non-deterministic state monad.
-/
def interpreter (handler : (eff : InstructionEffect) → NEStateM String σ eff.ret)
    : SailM α → NEStateM String σ α :=
  FreeM.liftM (fun
    | .inl (.error err) => Except.error err.print
    | .inl (.ok eff) => handler eff
    | .inr choice => NEStateM.chooseFin choice)

/--
Run one instruction on thread `tid` using the instruction semantics provided by `isem`.
-/
def runThreadInstruction (isem : SailM Unit) (tid : Fin n) : NEStateM String (ModelState n) Unit := do
  let mstate ← get
  let handler (eff : InstructionEffect)
      : NEStateM String ProjectedModelState eff.ret := do
    return (←runEffect tid mstate.initmem eff).fst
  /-
  The interpreter runs on a single thread (ProjectedModelState) which we
  lift up into a full model state (ModelState) monad.
  -/
  NEStateM.liftStateFull (projectModelState tid) (injectModelState tid) (interpreter handler isem)

/-- Promise that thread `tid` will do the write specified by `msg`. -/
def promiseMsg (tid : Fin n) (msg : Msg) (mstate : ModelState n) : ModelState n :=
  {
    mstate with
    mem := msg :: mstate.mem
    /- A Vector.getSet function would make this cleaner. -/
    threadStates := mstate.threadStates.set tid
      (mstate.threadStates[tid].promise (mstate.mem.length + 1))
  }

/-- Run effect on thread, recording list of promises that can be made. -/
def runEffectWithPromise (tid : Nat) (initmem : InitialMem)
    (base : View) (eff : InstructionEffect)
    : NEStateM String (ListSet Msg × ProjectedModelState) eff.ret := do
  /- Run the effect on the ProjectedModelState. -/
  let (res, vpreOpt) ← NEStateM.liftStateFull Prod.snd
    (fun pmstate state => (state.fst, pmstate) )
    (runEffect tid initmem eff)
  match vpreOpt with
  | .some vpre =>
    if vpre ≤ base then
      let mem := (← get).snd.mem
      /-
      Take all promises after base (made by that effect) and add them to the
      list of possible new promises.
      -/
      let newProms := ListSet.ofList (mem.take (mem.length - base))
      modify (fun (l,s) => (l.union newProms,s))
      pure res
    else
      pure res
  | .none => pure res

/-- Run a thread until its termination condition, recording a list of promises it can make. -/
def runToTermination (tid : Fin n) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition n) (fuel : Nat) (base : View)
    : NEStateM String (ListSet Msg × ProjectedModelState) Bool := do
  match fuel with
  | 0 =>
    /- If out of fuel and still not terminated then return false. -/
    return false
  | fuel + 1 => do
    /- Run one instruction on this thread. -/
    let handler := runEffectWithPromise tid initmem base
    interpreter handler isem
    /-
    If we have terminated then return true.
    Otherwise, reset the inter-instruction state and run the next instruction.
    -/
    let ts := (← get).snd.threadState
    if termination tid ts.regMap then
      return true
    else
      modify (fun s => (s.fst, { s.snd with iis := IIS.init }))
      runToTermination tid initmem isem termination fuel base

structure EnumerationResult where
  promises : ListSet Msg
  finalStates : ListSet ThreadState
  errors : ListSet String
  outOfFuel : Bool

/--
Run a thread until its termination condition, recording the promises it can make,
the final states it can reach, and any errors it encountered.
-/
def enumerateResults (n : Nat) (fuel : Nat) (tid : Fin n) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition n) (ts : ThreadState) (mem : PromisingMemory) : EnumerationResult :=
  let base := mem.length
  let st : ListSet Msg × ProjectedModelState := (ListSet.empty, { threadState := ts, mem := mem, iis := IIS.init })
  let res := runToTermination tid initmem isem termination fuel base st
  let successStates := res.oks.map Prod.fst
  let outOfFuel := res.oks.any (fun r => not r.snd)
  let promises := (successStates.map Prod.fst).flatten.prune
  let finalStates := successStates.filterMap (fun (newProms, st) =>
    if newProms.isEmpty then some st.threadState else none)
  let errors := res.errors.filterMap (fun ((newProms, _), errMsg) =>
    if newProms.isEmpty then some errMsg else none)
  { promises := promises, finalStates := finalStates, errors := errors, outOfFuel := outOfFuel }

/-- Non-deterministically choose a promise that can be made by thread `tid`. -/
def promiseSelectTid (fuel : Nat) (mstate : ModelState n) (tid : Fin n)
    (isem : SailM Unit) (termination : TerminationCondition n) : NExcept String Msg := do
  let res := enumerateResults n fuel tid mstate.initmem isem termination mstate.threadStates[tid] mstate.mem
  if res.outOfFuel then
    NExcept.error "out of fuel"
  else
    NExcept.choose res.promises

/-- Take any promising step for that tid and promise it. -/
def promiseTid (fuel : Nat) (tid : Fin n) (isem : SailM Unit)
    (termination : TerminationCondition n) : NEStateM String (ModelState n) Unit := do
  let mstate ← get
  let ev ← promiseSelectTid fuel mstate tid isem termination
  modify (fun _ => promiseMsg tid ev mstate)

/--
Non-deterministically make a promise or run an instruction on any thread.
If a thread has reached termination then no progress is made in that thread.
This is used by the naive execution.
-/
def runStep (fuel : Nat) (isem : SailM Unit)
    (termination : TerminationCondition n) : NEStateM String (ModelState n) Unit := do
  let mstate ← get
  let tid ← NEStateM.chooseFin n
  if threadTerminated termination mstate tid then
    NEStateM.discard
  else
    match (← NEStateM.chooseFin 2) with
    | 0 => promiseTid fuel tid isem termination
    | 1 => runThreadInstruction isem tid

/-- A model state paired with proof it satisfies the termination condition. -/
structure TerminatedModelState (nThreads : Nat)
    (termination : TerminationCondition nThreads) where
  state : ModelState nThreads
  proof : all_threads_terminated termination state

/--
Computationally evaluate all the possible allowed final states according to the
promising model.
-/
def runNaive (fuel : Nat) (isem : SailM Unit) (n : Nat) (termination : TerminationCondition n)
    : NEStateM String (ModelState n) (TerminatedModelState n termination) := do
  match fuel with
  | 0 => NEStateM.error "Could not finish running within the size of the fuel"
  | fuel' + 1 =>
    let mstate ← get
    if h : all_threads_terminated termination mstate then
      pure { state := mstate, proof := h }
    else
      runStep fuel isem termination
      runNaive fuel' isem n termination

/--
Computationally evaluate all the possible allowed final states according to the
promising model with promise-first optimization. The size of fuel should be at
least `(# of promises) + max(# of instructions) + 1`.
-/
def runPromiseFirst (fuel : Nat) (isem : SailM Unit)
    (n : Nat) (termination : TerminationCondition n)
    : NEStateM String (ModelState n) (TerminatedModelState n termination) := do
  if fuel == 0 then NEStateM.error "Promise first: out of fuel in main loop" else
  let fuel := fuel - 1
  let mstate ← get
  /- Find next possible promises or terminating states for each thread. -/
  let executionResults := Vector.ofFn (fun tid =>
    enumerateResults n fuel tid mstate.initmem isem termination mstate.threadStates[tid] mstate.mem)
  /- Throw any out of fuel errors in execution results. -/
  if executionResults.toList.any EnumerationResult.outOfFuel then
    NEStateM.error "Promise first: out of fuel in enumeration"
  match (← NEStateM.chooseFin 3) with
  | 0 =>
    /- We can make any promise from any thread from those available in the execution results. -/
    let tid ← NEStateM.chooseFin n
    let nextEv ← NEStateM.choose executionResults[tid].promises
    modify (fun mstate => promiseMsg tid nextEv mstate)
    runPromiseFirst fuel isem n termination
  | 1 =>
    /-
    If there is some choice of final states from each thread that form a valid terminated model state
    then we can return it.
    -/
    let tstates ← executionResults.mapM (fun r => NEStateM.choose r.finalStates)
    let mstate : ModelState n := { threadStates := tstates, initmem := mstate.initmem, mem := mstate.mem }
    if !noPromises mstate then NEStateM.discard else
    if h : all_threads_terminated termination mstate then
      pure { state := mstate, proof := h }
    else
      NEStateM.discard
  | 2 =>
    /- Throw all errors in the execution results. -/
    let errs := executionResults.toList.map EnumerationResult.errors
    NEStateM.throwErrors (ListSet.ofList errs).flatten

/--
Convert a promising model (non-deterministic state monad on the promising ModelState)
to the more abstract ComputationalTerminatingModel.
-/
def promisingRuntimeToModel
    (run : (n : Nat) → (termination : TerminationCondition n)
         → NEStateM String (ModelState n) (TerminatedModelState n termination))
    : ComputationalTerminatingModel :=
  fun (nThreads : Nat) (termCond : TerminationCondition nThreads)
      (archState : ArchState nThreads) =>
    let initmem := InitialMem.ofMemoryMap archState.memory
    let threadStates := archState.regs.map ThreadState.init
    let mState : ModelState nThreads := { initmem, threadStates, mem := [] }
    let output := run nThreads termCond mState
    let errors : ListSet (ModelResult nThreads Unit termCond) :=
      output.errors.map (fun (_,msg) => ModelResult.error msg)
    let results : ListSet (ModelResult nThreads Unit termCond) :=
      (output.oks.map (fun (_,final) =>
        let archState := final.state.toArchState
        let proof := terminated_model_state_to_arch_state final.proof
        ModelResult.finalState archState proof))
    -- TODO: do a faster hash-based prune here
    errors.union results.prune

/--
The naive model is more obviously correct than the promiseFirstModel, but
is inefficient because it is more exhaustive than it needs to be.
-/
def createNaiveModel (isem : SailM Unit) (fuel : Nat) : ComputationalTerminatingModel :=
  promisingRuntimeToModel (runNaive fuel isem)

/--
The promiseFirstModel should be equivalent to the naiveModel (TODO: prove this)
and it is more efficient.
-/
def createPromiseFirstModel (isem : SailM Unit) (fuel : Nat) : ComputationalTerminatingModel :=
  promisingRuntimeToModel (runPromiseFirst fuel isem)

end ModelEvaluation

end ArchSemTinyArm.Promising

import Out.Defs
import Out.TinyArm
import ArchsemLean.Sequential
import ArchsemLean.ExecutionMonad
import ArchsemLean.Common

open Sail.ArchSem
open ExecutionMonad

/- CR clang: copy over the descriptive comments from archsem. -/
/- CR clang: I should comment this code making references to the paper. https://sf.snu.ac.kr/publications/promising-arm-riscv.pdf -/

abbrev Loc := BitVec 53
abbrev Value := BitVec 64
abbrev Timestamp := Nat
abbrev View := Timestamp

/- CR clang: I would prefer WriteMsg or something. -/
structure Msg where
  tid : Nat
  loc : Loc
  val : Value
deriving DecidableEq

/- CR clang for thibaut: Maybe I should combine InitialMem and Memory into a struct? Maybe bring in definition of Msg? -/
def InitialMem := Std.ExtHashMap Loc Value
/- CR clang: should I rename to 'promising memory' or something? -/
abbrev Memory := List Msg

structure FwdItem where
  time : Timestamp
  view : View
  xcl : Bool

structure ThreadState where
  promises : List Timestamp
  regs : Std.ExtDHashMap Arch.register (fun reg => (Arch.register_type reg) × View)
  /- CR clang: I dont like the name 'coh' but the paper uses it and so does Archsem. -/
  coh : Std.ExtHashMap Loc View

  /- CR clang: rename these variables to something better. I dont see how this
     corresponds to the paper.-/
  vrd    : View /- The maximum output view of a read -/
  vwr    : View /- The maximum output view of a write -/
  vdmbst : View /- The maximum output view of a dmb st -/
  vdmb   : View /- The maximum output view of a dmb ld or dmb sy -/
  vcap   : View /- The maximum output view of control or address dependency -/
  visb   : View /- The maximum output view of an isb -/
  vacq   : View /- The maximum output view of an acquire access -/
  vrel   : View /- The maximum output view of an release access -/

  /- CR clang: 'forward bank' I dont like this name but its in paper and ArchSem. -/
  fwdb : Std.ExtHashMap Loc FwdItem
  /- CR clang: 'load exclusive' -/
  xclb : Option (Nat × View)


def Loc.fromAddr (addr : BitVec 56) : Option Loc :=
  if BitVec.extractLsb 0 3 addr == BitVec.zero 3 then
    .some (BitVec.extractLsb 55 3 addr)
  else .none

/- All memory accesses 8 byte aligned. -/
def InitialMem.read (init : InitialMem) (loc : Loc) : Option Value := init.get? loc

def Memory.lookup (t : Timestamp) (mem : Memory) : Option Msg :=
  if t == 0 then .none
  else if t <= mem.length then mem[mem.length - t]?
  else .none
def Memory.cutBefore (t : Timestamp) (mem : Memory) : Memory :=
  List.drop (mem.length - t) mem
def Memory.cutAfter (t : Timestamp) (mem : Memory) : Memory :=
  List.take (mem.length - t) mem
def Memory.attachTimestamps (mem : Memory) : List (Msg × Timestamp) :=
  match mem with
  | [] => []
  | h :: t => (h, List.length mem) :: Memory.attachTimestamps t
def Memory.cutAfterWithTimestamps (t : Timestamp) (mem : Memory) : List (Msg × Timestamp) :=
  List.take (mem.length - t) (mem.attachTimestamps)

def readLast (loc : Loc) (init : InitialMem) (mem : Memory) : Option (Value × Timestamp) :=
  match mem with
  | [] => Option.map (·, 0) (init.read loc)
  | msg :: mem =>
    if msg.loc == loc then
      .some (msg.val, mem.length)
    else readLast loc init mem

def readInitial (loc : Loc) (init : InitialMem) (mem : Memory) : Option Value :=
  match readLast loc init mem with
  | .some (x, 0) => .some x
  | _ => .none

def read (loc : Loc) (v : View) (init : InitialMem) (mem : Memory)
    : Option (List (Value × Timestamp)) :=
  match mem.cutBefore v |> readLast loc init with
  | .none => .none /- `loc` not mapped in initial memory -/
  | .some first =>
    let lasts := mem.cutAfterWithTimestamps v
              |> List.filter (fun (msg, _) => msg.loc == loc)
              |> List.map (fun (msg, v) => (msg.val, v))
    .some (lasts ++ [first])

def promise (msg : Msg) (mem : Memory) : View × Memory :=
  let nmem := msg :: mem
  (nmem.length, nmem)

/- CR clang: is it really a view being retrned? -/
def fulfill (msg : Msg) (prom : List Timestamp) (mem : Memory) : Option View :=
  prom.filter (fun t => mem.lookup t == .some msg)
    |> List.reverse
    |> List.head?

def exclusive (loc : Loc) (t : Timestamp) (mem : Memory) : Bool :=
  match mem.lookup t with
  | .none => false
  | .some msg =>
    if msg.loc == loc then
      List.all (mem.cutAfter t)
        (fun (msg' : Msg) => (msg'.tid == msg.tid) || !(msg'.loc == msg.loc))
    else false

def FwdItem.init : FwdItem := { time := 0, view := 0, xcl := false }

/- CR clang: the archsem implementation takes an unused memory map? -/
def ThreadState.init (regs : Std.ExtDHashMap Arch.register Arch.register_type) : ThreadState :=
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
def ThreadState.regMap (ts : ThreadState) : Std.ExtDHashMap Arch.register Arch.register_type :=
  ts.regs.map (fun _r (rv,_) => rv)
/- CR clang: do I even use these setters? -/
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
def ThreadState.setLoadExclusive (vs : Nat × View) (ts : ThreadState) : ThreadState :=
  { ts with xclb := .some vs }
def ThreadState.clearLoadExclusive (ts : ThreadState) : ThreadState :=
  { ts with xclb := .none }

/- CR clang: idk if I like this... -/
/- CR clang: maybe better to just explicitly update ThreadState -/
inductive ThreadStateView where
  | vrd | vwr | vdmbst | vdmb | vcap | visb | vacq | vrel
  deriving BEq, Hashable, Repr
def ThreadState.update (ts : ThreadState) (field : ThreadStateView) (v : View) : ThreadState :=
  match field with
  | .vrd => { ts with vrd := max v ts.vrd }
  | .vwr => { ts with vwr := max v ts.vwr }
  | .vdmbst => { ts with vdmbst := max v ts.vdmbst }
  | .vdmb => { ts with vdmb := max v ts.vdmb }
  | .vcap => { ts with vcap := max v ts.vcap }
  | .visb => { ts with visb := max v ts.visb }
  | .vacq => { ts with vacq := max v ts.vacq }
  | .vrel => { ts with vrel := max v ts.vrel }

def ThreadState.promise (v : View) (ts : ThreadState) : ThreadState :=
  { ts with promises := v :: ts.promises }

/- INSTRUCTION SEMANTICS -/

/- CR clang: Check if I actually need this. -/
def viewIf (b : Bool) (v : View) := if b then v else 0

/-
CR clang: move this into the interface.
I got this from ArchSem/Interface.v but is it even right? Why not a locical OR?
-/
def isRelAcq (macc : Arch.mem_acc) : Bool :=
  Arch.mem_acc_is_rel_acq_rcsc macc && Arch.mem_acc_is_rel_acq_rcpc macc 

/- CR clang: maybe namespace this into FwdItem. -/
def readFwdView (macc : Arch.mem_acc) (f : FwdItem) : View :=
  if f.xcl && (isRelAcq macc) then f.time else f.view

def readMem (loc : Loc) (vaddr : View) (macc : Arch.mem_acc)
    (init : InitialMem) (mem : Memory)
    : NEStateM ThreadState String (Timestamp × Value) := do
  if Arch.mem_acc_is_atomic_rmw macc then Except.error "Atomic RMW unsupported"
  let ts ← get
  let vbob := max ts.vdmb ts.visb |>.max ts.vacq
    |>.max (viewIf (Arch.mem_acc_is_rel_acq_rcsc macc) ts.vrel)
  let vpre := max vaddr vbob
  let vread := max vpre (ts.coh.getD loc 0)
  let reads ← match read loc vread init mem with
  | .none => Except.error "Reading from unmapped memory"
  | .some reads => pure reads
  /- CR clang: why does the monadLift not happen automatically? -/
  /- CR clang: Give NResult.fromResults an easier name like `choose reads`. -/
  let (res, time) ← liftM (m := NResult String) (n := NEStateM ThreadState String) (NResult.fromResults reads)
  let read_view :=
    match ts.fwdb.get? loc with
    | some fwd => if fwd.time == time then readFwdView macc fwd else time
    | none => time
  let vpost := max vpre read_view
  modify (fun ts => ts.updateCoherenceView loc time)
  modify (fun ts => ts.update .vrd vpost)
  modify (fun ts => ts.update .vacq (viewIf (isRelAcq macc) vpost))
  modify (fun ts => ts.update .vcap vaddr)
  if Arch.mem_acc_is_exclusive macc then
    modify (fun ts => ts.setLoadExclusive (time, vpost))
  return (vpost, res)

/- CR clang: TODO sanity check some of these bitwise operations. -/
def readMem4 (addr : Loc) (macc : Arch.mem_acc) (init : InitialMem) :
    NEStateM Memory String (BitVec 32) := do
  if Arch.mem_acc_is_ifetch macc then
    let aligned_addr := BitVec.and addr (BitVec.ofNat 56 0x03).not
    let bit2 := addr.getLsb 2
    let loc ← match Loc.fromAddr aligned_addr with
    | .none => Except.error "Address not supported"
    | .some loc => pure loc
    let mem ← get
    let block ← match readInitial loc init mem with
    | .none => Except.error s!"Modified instruction memory at {loc} {aligned_addr}"
    | .some block => pure block
    return (if bit2 then block.extractLsb 63 32 else block.extractLsb 31 0)
  else
    Except.error "Non-ifetch 4 bytes access"

def writeMem (tid : Nat) (loc : Loc) (vdata : View)
    (macc : Arch.mem_acc) (mem : Memory) (data : Value)
    : NEStateM ThreadState String (Memory × View × Option View) := do
  let msg := { tid, loc, val := data }
  let is_release := isRelAcq macc
  let ts ← get
  let (time, mem, new_promise) :=
    match fulfill msg ts.promises mem with
    | some t => (t, mem, false)
    | none =>
      let (view, newMem) := promise msg mem
      (view, newMem, true)
  let vbob :=
    max ts.vdmbst ts.vdmb |>.max ts.visb |>.max ts.vacq
    |>.max (viewIf is_release (max ts.vrd ts.vwr))
  let vpre := max vdata ts.vcap |>.max vbob
  if (max vpre (ts.coh.getD loc 0)) >= time then
    NEStateM.discard
  modify (fun ts => { ts with promises := ts.promises.filter (· != time) })
  modify (fun ts => ts.updateCoherenceView loc time)
  modify (fun ts => ts.update .vwr time)
  modify (fun ts => ts.update .vrel (viewIf is_release time))
  pure (mem, time, (if new_promise then some vpre else none))

def writeMemXcl (tid : Nat) (loc : Loc)
    (vdata : View) (macc : Arch.mem_acc)
    (mem : Memory) (data : Value)
    : NEStateM ThreadState String (Memory × Option View) := do
  if Arch.mem_acc_is_atomic_rmw macc then Except.error "Atomic RMW unsupported"
  let xcl := Arch.mem_acc_is_exclusive macc
  if xcl then
    let (mem, time, vpreOpt) ← writeMem tid loc vdata macc mem data
    let ts ← get
    match ts.xclb with
    | none => NEStateM.discard
    | some (xtime, _xview) =>
        if !(exclusive loc xtime (mem.cutAfter time)) then
          NEStateM.discard
    modify (fun ts => ts.setForwardingItem loc { time, view := vdata, xcl := true })
    modify (fun ts => ts.clearLoadExclusive)
    return (mem, vpreOpt)
  else
    let (mem, time, vpreOpt) ← writeMem tid loc vdata macc mem data
    modify (fun ts => ts.setForwardingItem loc { time, view := vdata, xcl := false })
    return (mem, vpreOpt)


section RunOutcome

/- CR clang: I dont understand this IIS and PartialPromisingState stuff. -/
/- CR clang for thibaut:
  Does PartialPromisingState really need to be its own structure? Why not inside TState?
  Do we really need a struct IIS containing just a view? Why not just inline it like I have done?
  Is there a better name for IIS or PartialPromisingState?
-/
/- Intra Instruction State -/
/-
structure IIS where
  strict : View
  deriving Inhabited
-/

structure ProjectedModelState where
  threadState : ThreadState
  mem : Memory
  iis : View /- CR clang: archsem abstracts here by IIS struct. -/


/-
def IIS.init : IIS := { strict := 0 }
def IIS.add (v : View) (iis : IIS) : IIS :=
  { iis with strict := iis.strict.max v }
-/

/- CR clang for thibaut:
  I dont understand the 'ComputeProm' stuff, its not mentioned in the paper.
  I see that a lot of it was remove in your PR "fix error propogation logic..."
  Why does runOutcome return a view, only to be handled by run_outcome_with_promise?
  What is the view that is returned?
  Whats the difference between CProm and ComputeProm in Archsem?
  Why have promises stored in CProm? We already have promises in ThreadState?
-/

/- CR clang: make sure to rename outcome to effect. -/
/- CR clang: it would be nice if the state lifts were implicit. -/
def runOutcome (tid : Nat) (initmem : InitialMem) (out : InstructionEffect)
    : NEStateM ProjectedModelState String ((InstructionEffect.ret out) × Option View) :=
  match out with
  | .regWrite reg racc val => do
    match racc with | none => pure () | some _ => Except.error "Non trivial reg access types unsupported"
    let vreg := (← get).iis
    let vreg' ←
      if reg == ._PC then
        modify (fun ps => { ps with threadState := ps.threadState.update .vcap vreg })
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
    /-
    /- CR clang: address space is unit for the lean model -/
    if memReq.addressSpace != PAS_NonSecure then  Except.error "Non trivial address space unsupported"
    -/
    match h : memReq.size with
    | 4 => /- ifetch -/
      /-
       - CR clang for leo: In archsem, rocq is able to auto-synthesize the setter given the getter.
       - could we add an NEStateM.liftState which is the analogous of archsem rocq's. This might require
       - a lean language feature but I'm not sure how we could do it.
       -/
      let opcode ← NEStateM.liftStateFull (ProjectedModelState.mem)
        (fun mem ppstate => { ppstate with mem := mem } )
        (readMem4 memReq.address memReq.accessKind initmem)
      return (.Ok (opcode, BitVec.zero 0), none)
    | 8 =>
      let loc ← match Loc.fromAddr memReq.address with
        | .none => Except.error "Physical address not supported"
        | .some loc => pure loc
      if Arch.mem_acc_is_ifetch memReq.accessKind then
        Except.error "TODO ifetch"
      else if Arch.mem_acc_is_explicit memReq.accessKind then
        let vaddr := (← get).iis
        let mem := (← get).mem
        /- CR clang: see my other comment about NEStateM.liftState -/
        let (view, val) ← NEStateM.liftStateFull ProjectedModelState.threadState
          (fun tstate ppstate => { ppstate with threadState := tstate })
          (readMem loc vaddr memReq.accessKind initmem mem)
        modify (fun s => { s with iis := s.iis.add view })
        /- CR clang: This `h` proof business is a bit ugly. Is there a nicer way? -/
        return (.Ok (Eq.symm h ▸ val, BitVec.zero 0), none)
      else Except.error "Read is not explicit or ifetch"
    | _ => Except.error "Memory read of size other than 8 and 4"
  | .memWriteAnnounce _ => do
    let vaddr := (← get).iis
    modify (fun s => { s with threadState := s.threadState.update .vcap vaddr })
    return ((), none)
  | .memWrite memReq val tags => do
    match h : memReq.size with
    | 8 =>
      let loc ← match Loc.fromAddr memReq.address with
        | .none => Except.error "Physical address not supported"
        | .some loc => pure loc
      if ¬Arch.mem_acc_is_explicit memReq.accessKind then Except.error "Unsupported non-explicit write"
      let mem := (← get).mem
      let vdata := (← get).iis
      /- CR clang: I feel like there must be a nicer way to do this. -/
      have h' : Value = BitVec (8 * memReq.size) := by rw [Value, h]
      /- CR clang: see my other comment about NEStateM.liftState -/
      let (mem, vpreOpt) ← NEStateM.liftStateFull ProjectedModelState.threadState
        (fun tstate ppstate => { ppstate with threadState := tstate } )
        (writeMemXcl tid loc vdata memReq.accessKind mem (h' ▸ val))
      modify (fun s => {s with mem := mem})
      return (.Ok (), vpreOpt)
    | _ => Except.error "Unsupported memory write size"
  | .barrier (Barrier.Barrier_DMB dmb) => do
    /- CR clang: I feel a bit weird here because we are kind of fetching threadState twice. -/
    let ts := (← get).threadState
    match dmb.types with
    | .MBReqTypes_All =>
      modify (fun s => { s with threadState := s.threadState.update .vdmb (max ts.vrd ts.vwr) })
    | .MBReqTypes_Reads =>
      modify (fun s => { s with threadState := s.threadState.update .vdmb ts.vrd })
    | .MBReqTypes_Writes =>
      modify (fun s => { s with threadState := s.threadState.update .vdmbst ts.vwr })
    return ((), none)
  | .barrier (Barrier.Barrier_ISB ()) => do
    let ts := (← get).threadState
    modify (fun s => { s with threadState := s.threadState.update .visb ts.vcap })
    return ((), none)
  /- CR clang: some more instructions needed here. clock, print, errors, tsb, etc -/
  | _ => Except.error "Unsupported effect"

/- CR clang: rename 'outcome' to 'effect'. -/
/- CR clang: I hate these "prime" functions. Come up with better names. -/
/-
/- CR clang: I just deleted it because we can just use runOutcome and pipe into fst -/
def runOutcome' (tid : Nat) (initmem : InitialMem) (out : InstructionEffect)
    : NEStateM ProjectedModelState String (InstructionEffect.ret out) := do
  let (ret, _opt) ← (runOutcome tid initmem out)
  return ret
  -/

end RunOutcome

structure Model where
  tState : Type
  tStateInit : Tid → InitialMem → RegisterMap → tState
  tStateRegs : tState → RegisterMap
  tStateNoPromises : tState → Bool
  iis : Type
  iisInit : iis
  memEvent : Type
  memEventDecidableEq : DecidableEq memEvent
  memEventTid : memEvent → Tid
  addressSpace : Arch.addr_space
  /- CR clang: check that it indeed is a view being returned from here. We had `Nat` in archsem. -/
  handleEffect : Tid → InitialMem → (eff : InstructionEffect)
    → NEStateM ProjectedModelState String (eff.ret × Option View)
  emitPromise : Tid → InitialMem → Memory → memEvent → tState → tState
  /- CR clang: This is weird, do I need it? -/
  checkValidEnd : Tid → InitialMem → Memory → tState → List String
  /- CR clang: add this back later.
  memorySnapshot : InitialMem → Memory → InitialMem
  -/

def UserModeModel : Model := {
  tState := ThreadState
  tStateInit := fun _tid _mem => ThreadState.init
  tStateRegs := ThreadState.regMap
  tStateNoPromises := fun tstate => tstate.promises.isEmpty
  iis := View
  iisInit := 0
  memEvent := Msg
  memEventDecidableEq := inferInstance
  memEventTid := Msg.tid
  addressSpace := () /- CR clang: in archsem was PASpace.PAS_NonSecure -/
  handleEffect := runOutcome
  emitPromise := fun _tid _initmem mem _msg => ThreadState.promise mem.length
  checkValidEnd := fun _tid _initmem _mem _tstate => []
}

/- CR clang: TODO namespacing and use the above struct. -/
/- CR clang: Do I like these names. If so, stop using `pstate` for ModelState variables. -/
structure ModelState (nThreads : Nat) where
  threadStates : Vector ThreadState nThreads
  initmem : InitialMem
  mem : Memory

def threadTerminated
    (termination : TerminationCondition n)
    (pstate : ModelState n)
    (tid : Fin n) : Bool :=
  termination tid pstate.threadStates[tid].regMap

def allThreadsTerminated
    (termination : TerminationCondition n)
    (pstate : ModelState n) : Bool :=
  (List.finRange n).all (threadTerminated termination pstate)

def noThreadPromises (pstate : ModelState n) (tid : Fin n) : Bool :=
  pstate.threadStates[tid].promises.isEmpty

def noPromises (pstate : ModelState n) : Bool :=
  pstate.threadStates.all (fun tstate => tstate.promises.isEmpty)
  
def projectModelState (tid : Fin n) (pstate : ModelState n) : ProjectedModelState :=
  { threadState := pstate.threadStates[tid], mem := pstate.mem, iis := 0 }

def injectModelState (tid : Fin n) (ppstate : ProjectedModelState) (pstate : ModelState n) : ModelState n :=
  { pstate with threadStates := pstate.threadStates.set tid ppstate.threadState, mem := ppstate.mem }

/- CR clang: In archsem-rocq this is handled more generally. So this is tempoary really. -/
def interpreter (handler : (eff : InstructionEffect) → NEStateM σ String (eff.ret))
    : SailM α → NEStateM σ String α
  | .pure x => return x
  | .impure (.Err err) _cont => Except.error (err.print)
  | .impure (.Ok eff) cont => do
    let x ← handler eff
    interpreter handler (cont x)

/- CR clang: `run_tid` in archsem. -/
def runThreadInstruction (isem : SailM Unit) (tid : Fin n) : NEStateM (ModelState n) String Unit := do
  let pstate ← get
  let handler (eff : InstructionEffect) := return (← runOutcome tid pstate.initmem eff).fst
  NEStateM.liftStateFull (projectModelState tid) (injectModelState tid) (interpreter handler isem)

/- def seq_step -/
-- def allowedPromisesTid (certified : Bool) (pstate : ModelState n) (tid : Fin n) (msg : Msg) : Prop := sorry
-- def step (certif : Bool) (pstate : ModelState n) : ModelState n → Prop := sorry

/- CR clang: a Vector.getSet function would make this cleaner. -/
def promiseTid (tid : Fin n) (msg : Msg) (pstate : ModelState n)
    : ModelState n :=
  {
    pstate with
    mem := msg :: pstate.mem
    threadStates := pstate.threadStates.set tid
      (pstate.threadStates[tid].promise pstate.mem.length)
  }
  


def runOutcomeWithPromise (tid : Nat) (initmem : InitialMem)
    (base : View) (out : InstructionEffect)
    : NEStateM (List Msg × ProjectedModelState) String (InstructionEffect.ret out) := do
  /- CR clang: see my other comment about NEStateM.liftState -/
  let (res, vpreOpt) ← NEStateM.liftStateFull Prod.snd
    (fun ppstate state => (state.fst, ppstate) )
    (runOutcome tid initmem out)
  match vpreOpt with
  | .some vpre =>
    if vpre ≤ base then
      let mem := (← get).snd.mem
      -- modify (fun s => (CProm.addIf mem vpre base s.fst, s.snd))
      modify (fun (l,s) => (mem.take (mem.length - base) ++ l,s))
      pure res
    else
      pure res
  | .none => pure res

def runToTermination (tid : Fin n) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition n) (fuel : Nat) (base : View)
    : NEStateM (List Msg × ProjectedModelState) String Bool := do
  match fuel with
  | 0 =>
    let ts := (← get).snd.threadState
    return (termination tid ts.regMap)
  | fuel + 1 => do
    let handler := runOutcomeWithPromise tid initmem base
    interpreter handler isem
    let ts := (← get).snd.threadState
    if termination tid ts.regMap then return true else
    modify (fun s => (s.fst, { s.snd with iis := 0 }))
    runToTermination tid initmem isem termination fuel base

structure EnumerationResult where
  promises : List Msg
  final_states : List ThreadState
  errors : List String
  out_of_fuel : Bool

def enumerateResults (fuel : Nat) (tid : Fin n) (initmem : InitialMem) (isem : SailM Unit)
    (termination : TerminationCondition n) (ts : ThreadState) (mem : Memory) : EnumerationResult :=
  let base := mem.length
  let execResult := runToTermination tid initmem isem termination fuel base
  let st : List Msg × ProjectedModelState := ([], { threadState := ts, mem := mem, iis := 0 })
  let res := execResult st
  let successStates := res.results.map Prod.fst
  let outOfFuel := res.results.any (fun r => not r.snd)
  let promises := (successStates.map Prod.fst).flatten.eraseDups
  let tstates := successStates.filterMap (fun (newProms, st) =>
    if newProms.isEmpty then some st.threadState else none)
  let errors := res.errors.filterMap (fun ((newProms, _), errMsg) =>
    if newProms.isEmpty then some errMsg else none)
  { promises := promises, final_states := tstates, errors := errors, out_of_fuel := outOfFuel }

def promiseSelectTid (fuel : Nat) (pstate : ModelState n) (tid : Fin n)
    (isem : SailM Unit) (termination : TerminationCondition n) : NResult String Msg := do
  let res := enumerateResults fuel tid pstate.initmem isem termination pstate.threadStates[tid] pstate.mem
  if res.out_of_fuel then
    match (← NResult.chooseFin 2) with
    | 0 => NResult.error "out of fuel"
    | 1 => NResult.fromResults res.promises
  else
    NResult.fromResults res.promises

def cpromiseTid (fuel : Nat) (tid : Fin n) (isem : SailM Unit)
    (termination : TerminationCondition n) : NEStateM (ModelState n) String Unit := do
  let pstate ← get
  let ev ← promiseSelectTid fuel pstate tid isem termination
  modify (fun _ => promiseTid tid ev pstate)

def runStep (fuel : Nat) (isem : SailM Unit)
    (termination : TerminationCondition n) : NEStateM (ModelState n) String Unit := do
  let pstate ← get
  let tid ← NEStateM.chooseFin n
  if threadTerminated termination pstate tid then NEStateM.discard
  else
    match (← NEStateM.chooseFin 2) with
    | 0 => cpromiseTid fuel tid isem termination
    | 1 => runThreadInstruction isem tid

/- CR clang: archsem-rocq return a `final` (ModelStae + proof it satisfied termination condition). -/
def run (fuel : Nat) (isem : SailM Unit) (termination : TerminationCondition n)
    : NEStateM (ModelState n) String (ModelState n) := do
  let pstate ← get
  if allThreadsTerminated termination pstate then
    pure pstate
  else
    match fuel with
    | 0 => NEStateM.error "Could not finish running within the size of the fuel"
    | fuel' + 1 =>
      runStep (fuel' + 1) isem termination
      run fuel' isem termination

/-
 - CR clang: archsem-rocq does not bother with the partial application of the termination condition
 - with the thread id. Probably best to follow that
 -/
/- CR clang: strange that NEStateM has two copies of the ModelState in the output. -/
partial def runPromiseFirst (fuel : Nat) (isem : SailM Unit)
    (termination : TerminationCondition n) : NEStateM (ModelState n) String (ModelState n) := do
  match fuel with
  | 0 => NEStateM.error "Promise first: out of fuel in main loop"
  | fuel' + 1 =>
    let pstate ← get
    let executionResults := Vector.ofFn (fun tid =>
      enumerateResults fuel tid pstate.initmem isem termination pstate.threadStates[tid] pstate.mem)
    match (← NEStateM.chooseFin 4) with
    | 0 =>
      let tid ← NEStateM.chooseFin n
      let nextEv ← NEStateM.results executionResults[tid].promises
      modify (fun pstate => promiseTid tid nextEv pstate)
      runPromiseFirst fuel' isem termination
    | 1 =>
      let tstates ← executionResults.mapM (fun r => NEStateM.results r.final_states)
      let pstate : ModelState n := { threadStates := tstates, initmem := pstate.initmem, mem := pstate.mem }
      if !noPromises pstate then NEStateM.discard else
      if !allThreadsTerminated termination pstate then NEStateM.discard else
      let errs :=
        List.ofFn (fun tid : Fin n => UserModeModel.checkValidEnd tid pstate.initmem pstate.mem pstate.threadStates[tid])
        |>.flatten
      if errs.isEmpty then
        pure pstate
      else
        NEStateM.errors errs
    | 2 =>
      let errs := executionResults.toList.map EnumerationResult.errors |>.flatten
      NEStateM.errors errs
    | 3 =>
      if executionResults.toList.any EnumerationResult.out_of_fuel then
        NEStateM.error "Promise first: out of fuel in enumeration"
      else
        NEStateM.discard

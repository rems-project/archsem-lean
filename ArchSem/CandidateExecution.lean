-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Std.Data.ExtTreeSet
import ArchSem.Trace
import Sail.ArchSem
import ArchSem.Defs
import ArchSem.TerminatingModel

open Sail.ArchSem
open ArchSem.TerminatingModel

-- TODO: add comments

namespace ArchSem.CandidateExecutions

abbrev Rel (α : Type) (cmp : α × α → α × α → Ordering := by exact compare) := Std.ExtTreeSet (α × α) cmp

namespace Rel

def union {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  Std.ExtTreeSet.union r₁ r₂

def intersection {α : Type} {cmp : α × α → α × α → Ordering} [Std.TransCmp cmp]
    (r₁ r₂ : Rel α cmp) : Rel α cmp :=
  Std.ExtTreeSet.inter r₁ r₂

end Rel


abbrev IMon [Arch] := FreeM (InstructionEffect ⊕ FinChoice)
def IEvent [Arch] : Type := FreeM.Event InstructionEffect
def ITrace [Arch] : Type → Type := FreeM.Trace InstructionEffect

namespace IEvent

variable [Arch]

def getReg (ev : IEvent) : Option Arch.register :=
  match ev.call with
  | .regRead reg _ => .some reg
  | .regWrite reg _ _ => .some reg
  | _ => .none


def getRegValue (ev : IEvent)
    : Option (Σ (r : Arch.register), Arch.register_type r) :=
  match h : ev.call with
  | .regRead reg _ =>
    have h_eq : Arch.register_type reg = InstructionEffect.ret ev.call := by
      simp [InstructionEffect.ret, h]
    let val : Arch.register_type reg := h_eq ▸ ev.ret
    .some ⟨reg, val⟩
  | .regWrite reg _ val => .some ⟨reg, val⟩
  | _ => .none

def getMemRequest (ev : IEvent) : Option MemRequest :=
  match ev.call with
  | .memRead memReq => .some memReq
  | .memWriteAnnounce memReq => .some memReq
  | .memWrite memReq _ _ => .some memReq
  | _ => .none

def getAddr (ev : IEvent) : Option Address := do
  let memReq ← ev.getMemRequest
  return memReq.address

def getMemValue (ev : IEvent) : Option (Σ n : Nat, BitVec (8 * n)) :=
  match h : ev.call with
  | .memRead req =>
    have h_eq : Except Arch.abort (BitVec (8 * req.size) × BitVec req.numTag) = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    match (h_eq ▸ ev.ret) with
    | Except.ok (val, _) => .some ⟨req.size, val⟩
    | Except.error _ => .none
  | .memWrite req val _ => .some ⟨req.size, val⟩
  | _ => .none

def getBarrier (ev : IEvent) : Option Arch.barrier :=
  match ev.call with
  | .barrier barrier => .some barrier
  | _ => .none

def getCacheOp (ev : IEvent) : Option Arch.cache_op :=
  match ev.call with
  | .cacheOp op => .some op
  | _ => .none

def getTlbi (ev : IEvent) : Option Arch.tlbi :=
  match ev.call with
  | .tlbOp tlbi => .some tlbi
  | _ => .none

def getTransStart (ev : IEvent) : Option Arch.trans_start :=
  match ev.call with
  | .translationStart ts => .some ts
  | _ => .none

def getTransEnd (ev : IEvent) : Option Arch.trans_end :=
  match ev.call with
  | .translationEnd te => .some te
  | _ => .none

section IsReg

variable (ev : IEvent) (p : (r : Arch.register) → Option Arch.sys_reg_id → Arch.register_type r → Prop)

def is_reg_read_with : Prop
  := match h : ev.call with
  | .regRead reg racc =>
    have h_eq : Arch.register_type reg = InstructionEffect.ret ev.call := by
      simp [InstructionEffect.ret, h]
    let val : Arch.register_type reg := h_eq ▸ ev.ret
    p reg racc val
  | _ => False

instance [h : ∀ r acc v, Decidable (p r acc v)] : Decidable (is_reg_read_with ev p) := by
  rw [is_reg_read_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_reg_write_with : Prop
  := match ev.call with
  | .regWrite reg racc val => p reg racc val
  | _ => False

instance [h : ∀ r acc v, Decidable (p r acc v)] : Decidable (is_reg_write_with ev p) := by
  rw [is_reg_write_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_reg_event_with : Prop := is_reg_read_with ev p ∨ is_reg_write_with ev p

end IsReg

def is_mem_read_req_with (ev : IEvent)
    (p : (req : MemRequest) → Except Arch.abort (BitVec (8 * req.size) × BitVec (req.numTag)) → Prop)
  := match h : ev.call with
  | .memRead req =>
    let h_eq : Except Arch.abort (BitVec (8 * req.size) × BitVec req.numTag) = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    p req (h_eq ▸ ev.ret)
  | _ => False

instance [h : ∀ req res, Decidable (p req res)] : Decidable (is_mem_read_req_with ev p) := by
  rw [is_mem_read_req_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_read_with (ev : IEvent)
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Prop) : Prop
  := is_mem_read_req_with ev (fun req res => match res with
       | .ok val => p req val.fst val.snd
       | .error _ => False)

instance [h : ∀ req val tags, Decidable (p req val tags)]
    : Decidable (is_mem_read_with ev p) := by
  rw [is_mem_read_with, is_mem_read_req_with] ; split
  · split
    · apply h
    · exact Decidable.isFalse False.elim
  · exact Decidable.isFalse False.elim

def is_mem_write_announce_with (ev : IEvent) (p : MemRequest → Prop) :=
  match ev.call with
  | .memWriteAnnounce req => p req
  | _ => False

instance [h : ∀ req, Decidable (p req)] : Decidable (is_mem_write_announce_with ev p) := by
  rw [is_mem_write_announce_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_write_req_with (ev : IEvent)
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Except Arch.abort Unit → Prop) : Prop
  := match h : ev.call with
  | .memWrite req val tags =>
    let h_eq : Except Arch.abort Unit = Effect.ret ev.call := by
      simp [Effect.ret, InstructionEffect.ret, h]
    p req val tags (h_eq ▸ ev.ret)
  | _ => False

instance [h : ∀ req val tags res, Decidable (p req val tags res)]
    : Decidable (is_mem_write_req_with ev p) := by
  rw [is_mem_write_req_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_mem_write_with (ev : IEvent)
    (p : (req : MemRequest) → BitVec (8 * req.size) → BitVec req.numTag → Prop) : Prop
  := is_mem_write_req_with ev (fun req val tags res => match res with
       | .ok () => p req val tags
       | .error _ => False)

instance [h : ∀ req val tags, Decidable (p req val tags)]
    : Decidable (is_mem_write_with ev p) := by
  rw [is_mem_write_with, is_mem_write_req_with] ; split
  · split
    · apply h
    · exact Decidable.isFalse False.elim
  · exact Decidable.isFalse False.elim

def is_barrier_with (ev : IEvent) (p : Arch.barrier → Prop) : Prop
  := match ev.call with
  | .barrier barrier => p barrier
  | _ => False

instance [h : ∀ barrier, Decidable (p barrier)]
    : Decidable (is_barrier_with ev p) := by
  rw [is_barrier_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_cache_op_with (ev : IEvent) (p : Arch.cache_op → Prop) : Prop
  := match ev.call with
  | .cacheOp op => p op
  | _ => False

instance [h : ∀ op, Decidable (p op)]
    : Decidable (is_cache_op_with ev p) := by
  rw [is_cache_op_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

def is_tlb_op_with (ev : IEvent) (p : Arch.tlbi → Prop) : Prop
  := match ev.call with
  | .tlbOp op => p op
  | _ => False

instance [h : ∀ op, Decidable (p op)]
    : Decidable (is_tlb_op_with ev p) := by
  rw [is_tlb_op_with] ; split
  · apply h
  · exact Decidable.isFalse False.elim

abbrev is_reg_read (ev : IEvent) := is_reg_read_with ev (fun _ _ _ => True)
abbrev is_reg_write (ev : IEvent) := is_reg_write_with ev (fun _ _ _ => True)
abbrev is_reg_event (ev : IEvent) := is_reg_event_with ev (fun _ _ _ => True)
abbrev is_mem_read_req (ev : IEvent) := is_mem_read_req_with ev (fun _ _ => True)
abbrev is_mem_read (ev : IEvent) := is_mem_read_with ev (fun _ _ _ => True)
abbrev is_mem_write_announce (ev : IEvent) := is_mem_write_announce_with ev (fun _ => True)
abbrev is_mem_write_req (ev : IEvent) := is_mem_write_req_with ev (fun _ _ _ _ => True)
abbrev is_mem_write (ev : IEvent) := is_mem_write_with ev (fun _ _ _ => True)
abbrev is_barrier (ev : IEvent) := is_barrier_with ev (fun _ => True)
abbrev is_cache_op (ev : IEvent) := is_cache_op_with ev (fun _ => True)
abbrev is_tlb_op (ev : IEvent) := is_tlb_op_with ev (fun _ => True)

def is_unsupported_event (ev : IEvent) : Prop :=
  is_mem_read_req_with ev (fun req _ => req.numTag ≠ 0) ∨
  is_mem_write_req_with ev (fun req _ _ _ => req.numTag ≠ 0)

end IEvent

inductive ITrace.matches_isa [Arch]
    : IMon α → ITrace α → Prop
  | stopped (f : FreeM (InstructionEffect ⊕ FinChoice) α) : matches_isa f .stopped
  | ret (a : α) : matches_isa (.pure a) (.ret a)
  | eff (eff : InstructionEffect) (k : eff.ret → FreeM (InstructionEffect ⊕ FinChoice) α)
      : matches_isa (.impure (.inl eff) k) (.openCall eff)
  | next (eff : InstructionEffect) (k : eff.ret → IMon α) (ret : eff.ret)
      (t : ITrace α)
      : matches_isa (k ret) t → matches_isa (.impure (.inl eff) k) (.cons (eff &→ ret) t)
  | choose (n : Nat) (i : Fin n) (k : Fin n → IMon α) (t : ITrace α)
      : matches_isa (k i) t → matches_isa (.impure (.inr n) k) t

structure Eid where
  tid : Nat
  iid : Nat
  ieid : Nat
deriving BEq

-- TODO: other Eid ordering relations?

def Eid.compare (a b : Eid) : Ordering :=
  if a.tid < b.tid
  then .lt
  else if a.tid > b.tid
  then .gt
  else if a.iid < b.iid
  then .lt
  else if a.iid > b.iid
  then .gt
  else if a.ieid < b.ieid
  then .lt
  else if a.ieid > b.ieid
  then .gt
  else .eq

instance : Ord Eid where
  compare := Eid.compare

instance : Std.TransCmp Eid.compare where
  isLE_trans := by sorry
  eq_swap := by sorry

instance : Std.TransCmp (compare : Eid → Eid → Ordering) := by
  change Std.TransCmp Eid.compare
  infer_instance

-- TODO: Eid ordering relations

structure PreCand [Arch] [ArchExtra] (nThreads : Nat) where
  init : ArchState nThreads
  events : Vector (List (ITrace Unit)) nThreads

namespace PreCand

variable [Arch] [ArchExtra]

def matches_isa (p : PreCand nThreads) (isem : IMon Unit) : Prop :=
  ∀ (tid : Fin nThreads), ∀ trace ∈ p.events[tid], trace.matches_isa isem

def is_complete (p : PreCand nThreads) : Prop :=
  ∀ (tid : Fin nThreads), ∀ trace ∈ p.events[tid], trace.snd = .ret ()

def lookupInstruction (p : PreCand nThreads) (tid iid : Nat)
    : Option (ITrace Unit) := do
  let threadTraces ← p.events[tid]?
  threadTraces[iid]?

def instructionList (p : PreCand nThreads) : List (Nat × Nat × ITrace Unit) :=
  p.events.toList.mapIdx
    (fun tid traces => traces.mapIdx (fun iid trace => (tid, iid, trace)))
  |>.flatten

theorem lookup_instruction_list (p : PreCand nThreads) (tid iid : Nat) (t : ITrace Unit)
    : lookupInstruction p tid iid = .some t ↔ (tid, iid, t) ∈ instructionList p := by
  sorry

def lookupIEvent (p : PreCand nThreads) (tid iid ieid : Nat) : Option IEvent := do
  let inst ← p.lookupInstruction tid iid
  inst.fst[ieid]?

def iEventList (p : PreCand nThreads) : List (Nat × Nat × Nat × IEvent) :=
  p.instructionList.map
    (fun (tid, iid, trace) => trace.fst.mapIdx (fun ieid ev => (tid, iid, ieid, ev)))
  |>.flatten

theorem lookup_ievent_list (p : PreCand nThreads) (tid iid ieid : Nat) (ev : IEvent)
    : lookupIEvent p tid iid ieid = .some ev ↔ (tid, iid, ieid, ev) ∈ p.iEventList := by
  sorry

def iEventList' (p : PreCand nThreads) : List (Eid × IEvent) :=
  p.iEventList |>.map (fun (tid, iid, ieid, ev) => ({tid, iid, ieid}, ev))

def eid_valid (p : PreCand nThreads) (eid : Eid) : Prop :=
  (lookupIEvent p eid.tid eid.iid eid.ieid).isSome

instance (p : PreCand nThreads) (eid : Eid) : Decidable (eid_valid p eid) := by
  simp [eid_valid]
  infer_instance

instance : GetElem (PreCand nThreads) Eid IEvent eid_valid where
   getElem (p : PreCand nThreads) (eid : Eid) (h : eid_valid p eid) : IEvent := by
     match h_lookup : lookupIEvent p eid.tid eid.iid eid.ieid with
     | .some ev => exact ev
     | .none =>
       rw [eid_valid] at h
       rw [←Option.not_isSome_iff_eq_none] at h_lookup
       contradiction

def collectEid (f : Eid → IEvent → Prop) (p : PreCand nThreads)
    [h : ∀ eid ev, Decidable (f eid ev)]
    : Std.ExtTreeSet Eid :=
  Std.ExtTreeSet.ofList (
    p.iEventList'
    |>.filter (fun (eid, event) => f eid event)
    |>.map Prod.fst
  )

def eids (p : PreCand nThreads) : Std.ExtTreeSet Eid := p.collectEid (fun _ _ => True)

def regReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_reg_read ev)
def pcReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_reg_read_with ev (fun reg _ _ => reg = ArchExtra.register_pc))

def regWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_reg_write ev)
def pcWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_reg_write_with ev (fun reg _ _ => reg = ArchExtra.register_pc))

def memReads (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_read ev)
def memReadReqs (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_read_req ev)

def memReadAborts (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_read_req_with ev (fun _ res => not res.isOk))

def memWriteAddrAnnounces (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_write_announce ev)
def memWrites (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_write ev)
def memWriteReqs (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_write_req ev)
def memWriteAborts (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_write_req_with ev (fun _ _ _ res => not res.isOk))

def readsByKind (p : PreCand nThreads) (q : Arch.mem_acc → Bool)
    : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_read_with ev (fun req _ _ => q req.accessKind))
def writesByKind (p : PreCand nThreads) (q : Arch.mem_acc → Bool)
    : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_mem_write_with ev (fun req _ _ => q req.accessKind))

def barriers (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_barrier ev)
def cacheOps (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_cache_op ev)
def tlbOps (p : PreCand nThreads) : Std.ExtTreeSet Eid :=
  p.collectEid (fun _ ev => IEvent.is_tlb_op ev)

def finalThreadRegisterMap (p : PreCand nThreads) (tid : Fin nThreads) : RegisterMap :=
  p.events[tid].foldl (fun regMap iTrace =>
    iTrace.fst.foldl (fun regMap event =>
      match event.call with
      | .regWrite reg _acc val =>
        -- TODO (think about): the operational models are able to throw an error
        -- here when there is an invalid access type.
        regMap.insert reg val
      | _ => regMap
    ) regMap
  )
  p.init.regs[tid]

def finalRegisterMaps (p : PreCand nThreads) : Vector RegisterMap nThreads :=
  Vector.ofFn (finalThreadRegisterMap p)

-- TODO:
-- gatherByKey (create map of keys to events)
-- sameKey (create equivalence relation)
-- sameThread (equivalence relation)
-- sameInstructionInstance (equiv rel)
-- ...

def collectEidByKey {K : Type} [Ord K] [Std.TransCmp (compare : K → K → Ordering)]
    (p : PreCand nThreads) (getKey : Eid → IEvent → Option K)
    : Std.ExtTreeMap K (Std.ExtTreeSet Eid) :=
  p.iEventList'.foldl (fun map (eid, event) =>
      match getKey eid event with
      | .some key => map.insert key ((map.getD key (Std.ExtTreeSet.empty (cmp := Eid.compare))).insert eid)
      | .none => map
    ) Std.ExtTreeMap.empty

-- TODO: move this function elsewhere
def setProd {cmp : α → α → Ordering} [Std.TransCmp cmp]
    {cmp' : α × α → α × α → Ordering} [Std.TransCmp cmp']
    (a b : Std.ExtTreeSet α cmp) : Std.ExtTreeSet (α × α) cmp' :=
  a.foldl (fun prod a =>
    b.foldl (fun prod b =>
      prod.insert (a, b)
    ) prod
  ) Std.ExtTreeSet.empty

def sameKey {K : Type} [Ord K] [Std.TransCmp (compare : K → K → Ordering)]
    (p : PreCand nThreads) (getKey : Eid → IEvent → Option K)
    : Rel Eid :=
  (collectEidByKey p getKey).foldl (fun acc _ eids =>
    Std.ExtTreeSet.union acc (setProd eids eids)
  ) Std.ExtTreeSet.empty

def sameThread (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid _ => .some eid.tid)

def sameInstructionInstance (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid _ => .some (eid.tid, eid.iid))

def intraInstructionOrder (p : PreCand nThreads) : Rel Eid :=
  p.sameInstructionInstance
  |>.filter (fun (a,b) => a.ieid < b.ieid)

def interInstructionOrder (p : PreCand nThreads) : Rel Eid :=
  p.sameThread
  |>.filter (fun (a,b) => a.iid < b.iid)

def programOrder (p : PreCand nThreads) : Rel Eid :=
  Rel.union p.interInstructionOrder p.intraInstructionOrder

def sameAddr (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun _ ev => ev.getAddr)

def sameMemValue (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun _ ev => ev.getMemValue)

def sameReg (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid ev => Option.map (eid.tid, ·) ev.getReg)

def sameRegSameValue (p : PreCand nThreads) : Rel Eid :=
  p.sameKey (fun eid ev => Option.map (eid.tid, ·) ev.getRegValue)

-- TODO: finish adding other relations starting from is_valid_init_reg_read and co.

end PreCand

structure Cand (nThreads : Nat) [Arch] [ArchExtra] where
  pre : PreCand nThreads
  memReadsFrom : Rel Eid
  regReadsFrom : Rel Eid
  coherence : Rel Eid
  exclusives : Rel Eid


namespace Cand

variable [Arch] [ArchExtra]

def eid_valid (c : Cand nThreads) : Eid → Prop := c.pre.eid_valid

instance (c : Cand nThreads) (eid : Eid) : Decidable (eid_valid c eid) := by
  simp [eid_valid]
  infer_instance

instance : GetElem (Cand nThreads) Eid IEvent eid_valid where
  getElem (c : Cand nThreads) (eid : Eid) (valid : c.eid_valid eid) : IEvent
    := c.pre[eid]

def finalWrites (c : Cand nThreads) : Std.ExtTreeMap Address (Eid × BitVec 8) :=
  c.pre.iEventList'.foldl (fun mem (eid, ev) =>
    match ev.call with
    | .memWrite req val tags =>
      (List.finRange req.size).foldl (fun mem (i : Fin req.size) =>
        -- CR clang for thibaut: What happens if this addition overflows?
        let addr := req.address + i.val
        let byte := (Sail.bitvec_to_vecbytes val)[i]
        match mem.get? addr with
        | .some (eid', byte') =>
          if c.coherence.contains (eid, eid')
          then mem.insert addr (eid, byte)
          else mem
        | .none => mem.insert addr (eid, byte)
      ) mem
    | _ => mem
  ) Std.ExtTreeMap.empty

def finalMemMap (c : Cand nThreads) : MemoryMap :=
  let writtenMem := (finalWrites c).map (fun _ (_,v) => v)
  Std.ExtTreeMap.union c.pre.init.memory writtenMem

def toArchState (c : Cand nThreads) : ArchState nThreads :=
  { memory := c.finalMemMap
  , addressSpace := c.pre.init.addressSpace
  , regs := c.pre.finalRegisterMaps
  }

def valid_rf (c : Cand nThreads) (wsrc rdst : Eid) : Prop :=
  Option.isSome (do
    let write ← c[wsrc]?
    -- TODO complete this and other similar definitions.
    return Option.some ()
  )

end Cand

inductive AxiomaticModel.Behavior (Flag : Type) where
  | allowed
  | rejected
  | flagged (f : Flag)

def AxiomaticModel [Arch] [ArchExtra] (Flag : Type)
  := (nThreads : Nat) → Cand nThreads
  → Except String (AxiomaticModel.Behavior Flag)

end ArchSem.CandidateExecutions

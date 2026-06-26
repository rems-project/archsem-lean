-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.Defs
import ArchSem.CandidateExecution
import ArchSemTinyArm.Defs

open ArchSem.CandidateExecutions
open ArchSem.TerminatingModel

namespace ArchSemTinyArm.SequentialAxiomatic

section DerivedRelations

variable (c : Cand nThreads)

abbrev int := c.pre.sameThread
abbrev iio := c.pre.intraInstructionOrder

abbrev RR := c.pre.regReads
abbrev RW := c.pre.regWrites
abbrev RE := RR c ∪ RW c
abbrev rrf := c.regReadsFrom
abbrev rfr := c.regFromReads

abbrev W := c.pre.memWrites
abbrev R := c.pre.memReads
abbrev M := (c.pre.readsByKind mem_acc_is_explicit) ∪ (c.pre.writesByKind mem_acc_is_explicit)
abbrev T := c.pre.readsByKind mem_acc_is_ttw
abbrev IF := c.pre.readsByKind mem_acc_is_ifetch
abbrev IR := c.initMemReads

def amo := c.atomicUpdate
def rmw := c.exclusives ∪ amo c

-- If we were mixed size we would need to re-think coherence.
def co := Δ W c ; c.coherence ; Δ W c ∩ c.pre.sameAddr
def coi := co c ∩ int c
def coe := co c \ coi c

def rf := c.memReadsFrom ; Δ R c
def rfi := rf c ∩ int c
def rfe := rf c \ rfi c
def fr := Δ R c ; c.memFromReads
def fri := fr c ∩ int c
def fre := fr c \ fri c

def po := c.pre.programOrder

def TE := c.pre.collectEidWith (fun _ ev => ev.is_arch_exception)
def ERET := c.pre.collectEidWith (fun _ ev => ev.is_return_exception)

end DerivedRelations

structure consistent (c : Cand nThreads) where
  total : Rel.acyclic (po c ∪ fr c ∪ co c ∪ rf c ∪ rfr c ∪ rrf c)
  atomic : ∅ = (rmw c ∩ (fre c ; coe c))

-- TODO: ArchSem rocq has a register whitelist. I dont understand why.
structure not_ub (c : Cand nThreads) where
  initial_reads : (T c ∪ IF c) ⊆ IR c
  register_write_permitted : ∅ = c.pre.collectEidWith (fun _ ev => ev.is_reg_write_with (fun _ acc _ => acc.isSome))
  register_read_permitted : ∅ = c.pre.collectEidWith (fun _ ev => ev.is_reg_read_with (fun _ acc _ => acc.isSome))
  memory_events_permitted : c.pre.memEvents ⊆ M c ∪ T c ∪ IF c
  no_exceptions : ∅ = TE c ∪ ERET c

theorem consistent.mk_iff (c : Cand nThreads)
    : consistent c
    ↔ Rel.acyclic (po c ∪ fr c ∪ co c ∪ rf c ∪ rfr c ∪ rrf c)
    ∧ ∅ = (rmw c ∩ (fre c ; coe c))
  := by
  apply Iff.intro
  · exact fun { total, atomic } => ⟨total, atomic⟩
  · exact fun ⟨total, atomic⟩ => { total, atomic }

theorem not_ub.mk_iff (c : Cand nThreads)
    : not_ub c
    ↔ (T c ∪ IF c) ⊆ IR c
    ∧ ∅ = c.pre.collectEidWith (fun _ ev => ev.is_reg_write_with (fun _ acc _ => acc.isSome))
    ∧ ∅ = c.pre.collectEidWith (fun _ ev => ev.is_reg_read_with (fun _ acc _ => acc.isSome))
    ∧ c.pre.memEvents ⊆ M c ∪ T c ∪ IF c
    ∧ ∅ = TE c ∪ ERET c
  := by
  apply Iff.intro
  · exact fun { initial_reads, register_write_permitted, register_read_permitted, memory_events_permitted, no_exceptions }
      => ⟨initial_reads, register_write_permitted, register_read_permitted, memory_events_permitted, no_exceptions⟩
  · exact fun ⟨ initial_reads, register_write_permitted, register_read_permitted, memory_events_permitted, no_exceptions ⟩
      => { initial_reads, register_write_permitted, register_read_permitted, memory_events_permitted, no_exceptions }

instance : Decidable (consistent c) := by
  rw [consistent.mk_iff]
  infer_instance

instance : Decidable (not_ub c) := by
  rw [not_ub.mk_iff]
  infer_instance

def model : AxiomaticModel Empty := fun _ c =>
  if consistent c then
    if not_ub c then
      .ok .allowed
    else
      .error "undefined behaviour"
  else
    .ok .rejected

end ArchSemTinyArm.SequentialAxiomatic

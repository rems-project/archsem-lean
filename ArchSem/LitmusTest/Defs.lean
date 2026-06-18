-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Sail.ArchSem
import ArchSem.TerminatingModel

open Sail.ArchSem
open ArchSem.TerminatingModel

namespace ArchSem.LitmusTest

variable [Arch] [ArchExtra]

/-- All defined memory in a litmus test is labeled with a memory kind. -/
inductive MemoryKind where
  | code
  | data
  | pageTable
deriving Repr

/-- Parse memory kinds from the '.archsem.toml' test format. -/
def MemoryKind.fromString? : String → Option MemoryKind
  | "code" => some .code
  | "data" => some .data
  | "pagetable" => some .pageTable
  | _ => .none

/--
Represents a contiguious defined block of memory with single MemoryKind
and optionally labeled with symbol `sym`.
-/
structure MemoryBlock where
  addr : Nat
  /-
  We need to record `step` so we know what size to use when comparing with this
  symbol in a final memory condition.
  -/
  step : Nat
  data : List (BitVec 8)
  sym : Option String
  kind : MemoryKind
deriving Repr

/-- Write `MemoryBlock` onto `MemoryMap`. -/
def MemoryBlock.insertIntoMemoryMap (mem : MemoryMap) (block : MemoryBlock)
    : MemoryMap :=
  block.data.foldl (fun (m, a) byte => (m.writeByte a byte, a + 1) ) (mem, block.addr)
  |> Prod.fst

/--
The quantifier to be used on the final condition as specified by a litmus test.
-/
inductive TestKind where
  | forall
  | exists
  | notExists
deriving Repr

/-- A location who's value might be considered in a final condition check. -/
inductive FinalConditionLoc where
  | reg (tid : Nat) (reg : String)
  | mem (sym : String)
deriving Repr, DecidableEq, Ord

/-
Define an ordering on locations so that we have a normalized order to print
them.
-/
instance : LE FinalConditionLoc where
  le a b := compare a b ≠ Ordering.gt
instance (a b : FinalConditionLoc) : Decidable (a ≤ b) := by
  change Decidable (compare a b ≠ Ordering.gt)
  infer_instance

/-- A assertion to be checked on termination state. -/
inductive FinalCondition where
  | equalLocLoc (l₁ l₂ : FinalConditionLoc)
  | equalLocLiteral (l : FinalConditionLoc) (v : Nat)
  | and (cs : List FinalCondition)
  | or (cs : List FinalCondition)
  | not (c : FinalCondition)
  | true
  | false
deriving Repr

/-- A parsed '.archsem.toml' litmus test. -/
structure TestRepr where
  arch : String
  /-- Name of the test e.g. "MP". -/
  name : String
  /-- List of initial register values for each thread. -/
  registers : List (List (String × RegValGen))
  /-- List of blocks in initial memory. -/
  memory : List MemoryBlock
  /-- List of PC values for each thread to terminate at. -/
  termCond : List (List Nat)
  /-- Which states should meet the final condition for the test to be considered OK. -/
  kind : TestKind
  /-- Condition to check at the final state. -/
  finalCondition : FinalCondition
deriving Repr

/--
A summary of the results of running a litmus test.
-/
structure LitmusTestResult where
  stateSummary : List (List (FinalConditionLoc × Nat))
  observedCount : Nat
  notObservedCount : Nat
  isOk : Bool

/--
A parsed litmus test confg toml file. This will likely be per-architecture.
-/
structure LitmusTestConfig where
  registerRenames : Std.HashMap String String
  defaultFuel : Nat
  arch : String

end ArchSem.LitmusTest

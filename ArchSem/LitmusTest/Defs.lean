-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

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

/-- A condition on an architecture-generic register checked at termination state. -/
inductive FinalRegisterCondition where
  | regEq : RegValGen → FinalRegisterCondition
  | regNe : RegValGen → FinalRegisterCondition
deriving Repr

/-- A condition on an architecture-generic thread checked at termination state. -/
structure FinalThreadCondition where
  tid : Tid
  regConditions : List (String × FinalRegisterCondition)
deriving Repr

/-- A condition on a memory location checked at termination state. -/
inductive FinalMemoryWordCondition
  | memEq (v : Nat)
  | memNe (v : Nat)
deriving Repr

/-- A condition on memory to be checked at termination state. -/
structure FinalMemoryCondition where
  sym : String
  addr : Nat
  size : Nat
  condition : FinalMemoryWordCondition
deriving Repr

/--
A condition to be checked on terminatin state.
In the '.archsem.toml' format this is an element of [[outcome]].
-/
inductive FinalCondition where
  | observable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition
  | unobservable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition
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
  /-- List of register values for each thread to terminate at. -/
  termCond : List (List (String × RegValGen))
  /-- List of conditions to check at the final state. -/
  finalConditions : List FinalCondition
deriving Repr

/--
Running a litmus test will result in this structure assuming no errors are
encountered. It is strinctly a function of the final architecture states.
-/
inductive LitmusTestResult
  | allowed
  | forbidden (reason : String)

end ArchSem.LitmusTest

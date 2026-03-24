import ArchSem.TerminatingModel
import Sail.ArchSem

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest

inductive MemoryKind where
  | code
  | data
  | pageTable

def MemoryKind.fromString? : String → Option MemoryKind
  | "code" => some .code
  | "data" => some .data
  | "pagetable" => some .pageTable
  | _ => .none

/-
 - We need to record `step` so we know what size to use when comparing with this
 - symbol in a final memory condition.
 -/
structure MemoryBlock where
  addr : Nat
  step : Nat
  data : List (BitVec 8)
  sym : Option String
  kind : MemoryKind

def MemoryBlock.insertIntoMemoryMap (mem : MemoryMap) (block : MemoryBlock)
    : MemoryMap :=
  block.data.foldl (fun (m, a) byte => (m.insertByte a byte, a + 1) ) (mem, block.addr)
  |> Prod.fst

inductive FinalRegisterCondition where
  | regEq : RegValGen → FinalRegisterCondition
  | regNe : RegValGen → FinalRegisterCondition

structure FinalThreadCondition where
  tid : Tid
  regConditions : List (String × FinalRegisterCondition)

inductive FinalMemoryWordCondition
  | memEq : Nat → FinalMemoryWordCondition
  | memNe : Nat → FinalMemoryWordCondition

structure FinalMemoryCondition where
  sym : String
  addr : Nat
  size : Nat
  condition : FinalMemoryWordCondition

-- CR clang: difference between observable and unobservable?
/--
 - A condition the system should be in when it terminates.
 - In the toml format this is an element of [[outcome]].
 -/
inductive FinalCondition where
  | Observable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition
  | Unobservable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition

structure TestRepr where
  arch : String
  name : String
  registers : List (List (String × RegValGen))
  memory : List MemoryBlock
  termCond : List (List (String × RegValGen))
  finalConditions : List FinalCondition

end ArchSem.LitmusTest

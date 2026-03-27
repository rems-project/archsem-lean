import ArchSem.TerminatingModel
import Sail.ArchSem

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest

inductive MemoryKind where
  | code
  | data
  | pageTable
deriving Repr

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
deriving Repr

def MemoryBlock.insertIntoMemoryMap (mem : MemoryMap) (block : MemoryBlock)
    : MemoryMap :=
  block.data.foldl (fun (m, a) byte => (m.writeByte a byte, a + 1) ) (mem, block.addr)
  |> Prod.fst

inductive FinalRegisterCondition where
  | regEq : RegValGen → FinalRegisterCondition
  | regNe : RegValGen → FinalRegisterCondition
deriving Repr

structure FinalThreadCondition where
  tid : Tid
  regConditions : List (String × FinalRegisterCondition)
deriving Repr

inductive FinalMemoryWordCondition
  | memEq : Nat → FinalMemoryWordCondition
  | memNe : Nat → FinalMemoryWordCondition
deriving Repr

structure FinalMemoryCondition where
  sym : String
  addr : Nat
  size : Nat
  condition : FinalMemoryWordCondition
deriving Repr

/--
 - A condition the system should be in when it terminates.
 - In the toml format this is an element of [[outcome]].
 -/
inductive FinalCondition where
  | observable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition
  | unobservable : List FinalThreadCondition → List FinalMemoryCondition → FinalCondition
deriving Repr

structure TestRepr where
  arch : String
  name : String
  registers : List (List (String × RegValGen))
  memory : List MemoryBlock
  termCond : List (List (String × RegValGen))
  finalConditions : List FinalCondition
deriving Repr

end ArchSem.LitmusTest

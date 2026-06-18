-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Lake.Toml
import Lake.Toml.ParserUtil
import Sail
import ArchSem.Defs
import ArchSem.LitmusTest.Defs

/-!
This file implements parsing of '.archsem.toml' litmus tests.
Some of the code is a bit messy because the test format keeps changing.
-/

open ArchSem.LitmusTest

namespace ArchSem.LitmusTest.Parse

/- Helper functions for parsing tomls in Except monad. -/
def tomlFindStringElse (table : Lake.Toml.Table) (name : Lean.Name) (e : ε)
    : Except ε String :=
  match table.find? name with
  | .some (.string _ s) => pure s
  | _ => Except.error e
def tomlFindIntElse (table : Lake.Toml.Table) (name : Lean.Name) (e : ε)
    : Except ε Int :=
  match table.find? name with
  | .some (.integer _ n) => pure n
  | _ => Except.error e
def tomlFindNatElse (table : Lake.Toml.Table) (name : Lean.Name) (e : String)
    : Except String Nat := do
  let n ← tomlFindIntElse table name e
  if n < 0 then Except.error (e ++ " (excepting Nat found negative Int)")
  pure n.toNat
def tomlFindTableElse (table : Lake.Toml.Table) (name : Lean.Name) (e : String)
    : Except String Lake.Toml.Table :=
  match table.find? name with
  | .some (.table _ t) => pure t
  | _ => Except.error e

-- TODO: prove termination.
/-- Parse one RegValueGen. -/
partial def tomlToRegValGen : Lake.Toml.Value → Except String RegValGen
  | .integer _ i => .ok (.number i)
  | .string _ s => .ok (.string s)
  | .array _ l => do
    let a ← l.mapM (tomlToRegValGen)
    pure (.array a.toList)
  | .table _ t => do
    let t ← t.items.mapM (fun (k,v) => do pure (k.toString false, (← tomlToRegValGen v)))
    pure (.struct t.toList)
  | _ => .error "Failed to parse register value"

/--
Parse a register mapping table e.g.
  _PC = 0x500
  "R0" = 0x1000
  "R1" = 0x100
  "R2" = 0x2a
  "R3" = 0x1000
  "R4" = 0x200
  "R5" = 1
-/
def tomlToThreadRegisters (regs : Lake.Toml.Table)
    : Except String (List (String × RegValGen)) := do
  let a ← regs.items.mapM (fun (k,v) => do pure (k.toString false, (← tomlToRegValGen v)))
  pure a.toList

/--
Parse registers for all threads e.g.
  ["0".regs]
    _PC = 0x500
    "R0" = 0x1000
    "R1" = 0x100
  ["1".regs]
    _PC = 0x600
    "R0" = 0x1000
    "R1" = 0x100
-/
def tomlToRegisters (threads : Lake.Toml.Table)
    : Except String (List (List (String × RegValGen))) := do
  let threadTables ← threads.items.toList.filterMap (fun (k, v) => match (k.toString false).toNat? with
    | .some tid => .some (tid, v)
    | .none => .none)
  |>.mapM (fun (tid, v) => match v with
    | .table _ t => return (tid, t)
    | _ => Except.error "Failed to parse thread register: expected table")
  threadTables.mergeSort (fun a b => a.1 <= b.1)
  |>.mapIdxM (fun i (tid, t) =>
    if i != tid
    then Except.error s!"Missing thread '{i}'"
    else do
      let regs ← match t.find? `regs with
        | .some (.table _ regs) => pure regs
        | _ => Except.error "Failed to parse thread register: expected regs table"
      tomlToThreadRegisters regs
  )

/--
Termination condition used to be an arbitrary predicate on register state,
but it has since changed to a list of "breakpoints" on each thread.
When a thread reaches any one of its breakpoints, it is considered terminated.
e.g.
  ["0"]
    breakpoints = [0x508]
  ["1"]
    breakpoints = [0x608]
-/
def tomlToTermCond (threads : Lake.Toml.Table)
    : Except String (List (List Nat)) := do
  let threadTables ← threads.items.toList.filterMap (fun (k, v) => match (k.toString false).toNat? with
    | .some tid => .some (tid, v)
    | .none => .none)
  |>.mapM (fun (tid, v) => match v with
    | .table _ t => return (tid, t)
    | _ => Except.error "Failed to parse thread register: expected table")
  threadTables.mergeSort (fun a b => a.1 <= b.1)
  |>.mapIdxM (fun i (tid, t) =>
    if i != tid
    then Except.error s!"Missing thread '{i}'"
    else
      match t.find? `breakpoints with
      | .some (.array _ breakpoints) => breakpoints.toList.mapM (fun b => match b with
        | .integer _ i => return i
        | _ => Except.error "Breakpoint must be integer")
      | _ => Except.error "Failed to parse thread register: expected breakpoints array"
  )


/-- Parse a memory block. e.g. an element of `[[memory]]`. -/
def tomlToMemoryBlock (table : Lake.Toml.Table) : Except String MemoryBlock := do
  let addr ← tomlFindNatElse table `addr "Failed to parse memory block addr"
  let step ← tomlFindNatElse table `step "Failed to parse memory block step"
  let data ← match table.find? `data with
    | .some (.array  _ a) => do
      let bytesList ← a.toList.mapM (fun v => match v with
        | .integer _ i => do
          if i < 0 then Except.error "Failed to parse memory block data (negative element)"
          let bitvec := BitVec.ofNat (8 * step) i.toNat
          let bytes := Sail.bitvec_to_vecbytes bitvec
          pure bytes.toList
        | _ => Except.error "Failed to parse memory block data element")
      pure bytesList.flatten
    | .some (.integer _ i) => do
      if i < 0 then Except.error "Failed to parse memory block data (negative)"
      let bitvec := BitVec.ofNat (8 * step) i.toNat
      let bytes := Sail.bitvec_to_vecbytes bitvec
      pure bytes.toList
    | _ => Except.error "Failed to parse memory block data"
  let sym ← match table.find? `sym with
    | .some (.string _ s) => pure (Option.some s)
    | .none => pure none
    | _ => Except.error "Failed to parse memory block sym field"
  let kind ← match table.find? `kind with
    | .some (.string _ s) => (match MemoryKind.fromString? s with
      | .some k => pure k
      | .none => Except.error s!"Invalid memory kind '{s}'")
    | .none => pure MemoryKind.data
    | _ => Except.error "Failed to parse memory block kind"
  pure { addr, step, data, sym, kind }

/-- Parse `[[memory]]`. Representing a list of memory blocks. -/
def tomlToMemory (memory : Array Lake.Toml.Value) : Except String (List MemoryBlock) :=
  memory.toList.mapM (fun block => match block with
    | .table _ t => tomlToMemoryBlock t
    | _ => Except.error "Failed to parse memory block")

/--
Parse a final condition location e.g.
  "1:R5"
or
  "x"
-/
def stringToFinalConditionLoc (s : String) : Except String FinalConditionLoc :=
  match s.splitOn ":" with
  | [thread, reg] =>
    match String.toNat? thread with
    | .none => Except.error s!"Failed to parse final condition register location '{s}'"
    | .some thread => return .reg thread reg
  | [sym] => return .mem sym
  | _ => Except.error s!"Failed to parse final condition location '{s}'"

mutual

-- TODO: prove termination.
/-- Parse a final condition e.g. `{and = [{"1:R5" = 1}, {"1:R2" = 0}]}`. -/
partial def tomlToFinalCondition (condition : Lake.Toml.Table)
    : Except String FinalCondition := do
  match condition.items.toList with
  | [(`and, .array _ a)] =>
    return .and (← tomlToFinalConditions a)
  | [(`or, .array _ a)] =>
    return .or (← tomlToFinalConditions a)
  | [(`not, .table _ c)] =>
    return .not (← tomlToFinalCondition c)
  | [(`and, _)] => Except.error "Failed to parse final condition: `and` expects array"
  | [(`or, _)] => Except.error "Failed to parse final condition: `or` expects array"
  | [(`not, _)] => Except.error "Failed to parse final condition: `not` expects table"
  | [(k, .string _ s)] =>
    return .equalLocLoc (← stringToFinalConditionLoc (k.toString false)) (← stringToFinalConditionLoc s)
  | [(k, .integer _ v)] =>
    return .equalLocLiteral (← stringToFinalConditionLoc (k.toString false)) v
  | _ => Except.error s!"Failed to parse final condition: expected singleton assertion map"

partial def tomlToFinalConditions (finals : Array Lake.Toml.Value)
    : Except String (List FinalCondition) :=
  finals.toList.mapM (fun condition => match condition with
    | .table _ t => tomlToFinalCondition t
    | _ => Except.error "Failed to parse final conditions")

end

/-- Parse the toml file in '.archsem.toml' format. -/
def tomlToTestRepr (toml : Lake.Toml.Table) : Except String TestRepr := do
  let arch ← tomlFindStringElse toml `arch "Failed to parse 'arch' field"
  let name ← tomlFindStringElse toml `name "Failed to parse 'name' field"
  let (registers, termCond) ← match toml.find? `thread with
    | .some (.table _ t) => do
      pure ((← tomlToRegisters t), (← tomlToTermCond t))
    | _ => Except.error "Failed to find any threads"
  let memory ← match toml.find? `memory with
    | .some (.array _ a) => tomlToMemory a
    | _ => Except.error "Failed to parse 'memory' field"
  let kind : TestKind := .exists -- TODO: parse from file, default to exists
  let finalCondition ← match toml.find? `final with
    | .some (.table _ t) =>
      match t.find? `assertion with
      | .some (.table _ t) => tomlToFinalCondition t
      | _ => Except.error "Failed to parse 'assertion' field"
    | _ => Except.error "Failed to parse 'final' field"
  pure { arch, name, registers, termCond, memory, kind, finalCondition }

/-- Read and parse a toml file. -/
def readTomlFile (fname : System.FilePath) : IO Lake.Toml.Table := do
  let input ← IO.FS.readFile fname
  let ictx := Lean.Parser.mkInputContext input fname.toString
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
    | .ok t => pure t
    | .error log => do
      let logStr ← Lake.mkMessageLogString log
      throw (IO.Error.userError s!"Failed to parse TOML:\n{logStr}")

/-- Read and parse a file in '.archsem.toml' format. -/
def readTestFile (fname : System.FilePath) : IO TestRepr := do
  let table ← readTomlFile fname
  match Parse.tomlToTestRepr table with
  | .ok repr => pure repr
  | .error e => throw (IO.Error.userError s!"Failed to parse Litmus Test: {e}")

end ArchSem.LitmusTest.Parse

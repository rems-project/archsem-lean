import Lake.Toml.ParserUtil
import Sail

import Lake.Toml
import ArchsemLean.Common
import ArchsemLean.LitmusTest.Basic

open ArchSem.LitmusTest

namespace ArchSem.LitmusTest.Parse

/- Toml helper functions. -/
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

-- TODO: prove termination.
/--
 - Parse one RegValueGen. e.g. a value in [[registers]].
 -/
partial def tomlToRegValGen : Lake.Toml.Value → Except String RegValGen
  | .integer _ i => .ok (.number i)
  | .string _ s => .ok (.string s)
  | .array _ l => do
    let a ← l.mapM (tomlToRegValGen)
    pure (.array a.toList)
  | .table _ t => do
    let t ← t.items.mapM (fun (k,v) => do pure (k.toString, (← tomlToRegValGen v)))
    pure (.struct t.toList)
  | _ => .error "Failed to parse register value"

/--
 - Parse one element of [[registers]]. Representing an initial assignment
 - of one threads registers.
 -/
def tomlToThreadRegisters (regs : Lake.Toml.Table)
    : Except String (List (String × RegValGen)) := do
  let a ← regs.items.mapM (fun (k,v) => do pure (k.toString, (← tomlToRegValGen v)))
  pure a.toList

/--
 - Parse [[registers]] or [[termCond]]. Representing an assignment of register
 - in a number of threads.
 -/
def tomlToRegisters (threads : Array Lake.Toml.Value)
    : Except String (List (List (String × RegValGen))) :=
  threads.toList.mapM (fun threadRegs => match threadRegs with
    | .table _ t => tomlToThreadRegisters t
    | _ => Except.error "Failed to parse register list")

/--
 - Parse a memory block. e.g. an element of [[memory]].
 -/
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

/--
 - Parse [[memory]]. Representing a list of memory blocks.
 -/
def tomlToMemory (memory : Array Lake.Toml.Value) : Except String (List MemoryBlock) :=
  memory.toList.mapM (fun block => match block with
    | .table _ t => tomlToMemoryBlock t
    | _ => Except.error "Failed to parse memory block")

def tomlToFinalRegisterConditions (table : Lake.Toml.Table)
    : Except String (List (String × FinalRegisterCondition)) :=
  table.items.toList.mapM (fun (reg, cond) => do
    let cond ← match cond with
      | .table _ cond => pure cond
      | _ => Except.error "Failed to parse final register condition"
    let op ← tomlFindStringElse cond `op "Failed to parse register condition op"
    let val ← match cond.find? `val with
    | .some v => tomlToRegValGen v
    | .none => Except.error "Failed to find register condition value"
    match op with
    | "eq" => pure (reg.toString, FinalRegisterCondition.regEq val)
    | "ne" => pure (reg.toString, FinalRegisterCondition.regNe val)
    | _ => Except.error s!"Invalid final register condition op '{op}'"
  )

def tomlToFinalThreadConditions (table : Lake.Toml.Table)
    : Except String (List FinalThreadCondition) := do
  let threadsTable ← match table.find? `regs with
    | some (.table _ t) => pure t
    | none => pure table
    | _ => Except.error "Failed to parse register final condition"
  threadsTable.items.toList.filterMapM (fun (tid, regs) => do
    let tid ← match tid.toString.toNat? with
      | some tid => pure tid
      | none => return none
    let regConditions ← match regs with
      | .table _ regsTable => tomlToFinalRegisterConditions regsTable
      | _ => Except.error "Failed to parse final register conditions"
    pure (some {tid , regConditions})
    )

def tomlToFinalMemoryWordCondition (toml : Lake.Toml.Value)
    : Except String FinalMemoryWordCondition :=
  match toml with
  | .table _ condTable => do
    let op ← tomlFindStringElse condTable `op "Failed to parse final memory condition op"
    let val ← tomlFindNatElse condTable `val "Failed to parse final memory condition value"
    match op with
    | "eq" => pure (.memEq val)
    | "ne" => pure (.memNe val)
    | _ => Except.error "Invalid op in final memory condition"
  | .integer _ i => do
    if i < 0 then Except.error "Failed to parse negative final memory condition"
    pure (.memEq i.toNat)
  | _ => Except.error "Failed to parse final memory word condition"

def tomlToFinalMemoryConditions (table : Lake.Toml.Table) (mem : List MemoryBlock)
    : Except String (List FinalMemoryCondition) :=
  match table.find? `mem with
  | .some (.table _ memTable) =>
    memTable.items.toList.mapM (fun (sym,v) => do
      let sym := sym.toString
      let condition ← tomlToFinalMemoryWordCondition v
      let block ← match List.find? (fun b => b.sym == some sym) mem with
        | .some b => pure b
        | .none => Except.error s!"Undefine memory symbol in final condition '{sym}'"
      pure { sym, addr := block.addr, size := block.step, condition }
    )
  | .none => pure []
  | _ => Except.error "Failed to parse final memory condition"

def tomlToFinalCondition (condition : Lake.Toml.Table) (mem : List MemoryBlock)
    : Except String FinalCondition := do
  match (condition.find? `observable, condition.find? `unobservable) with
  | (some (.table _ table), none) =>
    let threadConditions ← tomlToFinalThreadConditions table
    let memoryConditions ← tomlToFinalMemoryConditions table mem
    pure (.Observable threadConditions memoryConditions)
  | (none, some (.table _ table)) =>
    let threadConditions ← tomlToFinalThreadConditions table
    let memoryConditions ← tomlToFinalMemoryConditions table mem
    pure (.Observable threadConditions memoryConditions)
  | (some _, some _) => Except.error "Final condition can't have both observable and unobservable"
  | (none, none) => Except.error "Failed to parse empty final condition"
  | _ => Except.error "Failed to parse final condition"

/--
 - Parse [[outcome]]. Representing a list of final conditions.
 -/
def tomlToFinalConditions (finals : Array Lake.Toml.Value) (mem : List MemoryBlock)
    : Except String (List FinalCondition) :=
  finals.toList.mapM (fun condition => match condition with
    | .table _ t => tomlToFinalCondition t mem
    | _ => Except.error "Failed to parse final conditions")

def tomlToTestRepr (toml : Lake.Toml.Table) : Except String TestRepr := do
  let arch ← tomlFindStringElse toml `arch "Failed to parse 'arch' field"
  let name ← tomlFindStringElse toml `name "Failed to parse 'name' field"
  let registers ← match toml.find? `registers with
    | .some (.array _ a) => tomlToRegisters a
    | _ => Except.error "Failed to parse 'registers' field"
  let termCond ← match toml.find? `termCond with
    | .some (.array _ a) => tomlToRegisters a
    | _ => Except.error "Failed to parse 'termCond' field"
  let memory ← match toml.find? `memory with
    | .some (.array _ a) => tomlToMemory a
    | _ => Except.error "Failed to parse 'memory' field"
  let finalConditions ← match toml.find? `outcome with
    | .some (.array _ a) => tomlToFinalConditions a memory
    | _ => Except.error "Failed to parse 'outcome' field"
  pure { arch, name, registers, termCond, memory, finalConditions }

def readTomlFile (fname : System.FilePath) : IO Lake.Toml.Table := do
  let input ← IO.FS.readFile fname
  let ictx := Lean.Parser.mkInputContext input fname.toString
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
    | .ok t => pure t
    | .error log => do
      let logStr ← Lake.mkMessageLogString log
      throw (IO.Error.userError s!"Failed to parse TOML:\n{logStr}")

def readTestFile (fname : System.FilePath) : IO TestRepr := do
  let table ← readTomlFile fname
  match Parse.tomlToTestRepr table with
  | .ok repr => pure repr
  | .error e => throw (IO.Error.userError s!"Failed to parse Litmus Test: {e}")

end ArchSem.LitmusTest.Parse

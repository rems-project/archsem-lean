-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import ArchSem.LitmusTest.Defs
import ArchSem.LitmusTest.Parse

/-!
Parse litmus tests config file.
This config file should be per-architecture.
-/

open ArchSem.LitmusTest

namespace ArchSem.LitmusTest.Config

/--
Parse a register-rename table, mapping ISLA register names to archsem names e.g.
  X0 = "R0"
  X1 = "R1"
  X2 = "R2"
  ...
-/
def tomlToRegisterRenames (table : Lake.Toml.Table)
    : Except String (Std.HashMap String String) := do
  let pairs : List (String × String) ← table.items.toList.mapM (fun (k, v) =>
    match v with
    | .string _ s => pure (k.toString false, s)
    | _ => Except.error "Register maps may only map to strings")
  return Std.HashMap.ofList pairs

/--
Parse a LitmusTestConfig from the top-level toml table.
-/
def tomlToConfig (toml : Lake.Toml.Table) : Except String LitmusTestConfig := do
  let arch : String ← Parse.tomlFindStringElse toml `arch "Failed to parse 'arch' field"
  let execution : Lake.Toml.Table ← Parse.tomlFindTableElse toml `execution "Failed to find 'execution' table."
  let defaultFuel : Nat ← Parse.tomlFindNatElse execution `fuel "Failed to parse 'fuel' field"
  let registers : Lake.Toml.Table ← Parse.tomlFindTableElse toml `registers "Failed to find 'registers' table."
  let registerRenames ← match registers.find? `renames with
    | .some (.table _ t) => tomlToRegisterRenames t
    | _ => Except.error "Failed to find register remap table in config"
  return {arch, defaultFuel, registerRenames}

/--
Parse a LitmusTestConfig from a named file.
-/
def readConfigFile (fname : System.FilePath) : IO LitmusTestConfig := do
  let table ← Parse.readTomlFile fname
  match tomlToConfig table with
  | .ok config => pure config
  | .error e => throw (IO.Error.userError s!"Failed to parse litmus test config {fname}: {e}")

end ArchSem.LitmusTest.Config

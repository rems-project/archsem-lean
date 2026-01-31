import Out.Flow
import Out.Registers
import Out.Interface
import Out.Translation

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV2

namespace Out.Functions

open option
open ast
open VARange
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open Shareability
open SecurityState
open Register
open Regime
open PASpace
open PARTIDspaceType
open MemType
open MemTagType
open MemAtomicOp
open MBReqTypes
open MBReqDomain
open GPCF
open Fault
open ErrorState
open DeviceType
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open Barrier
open AccessType

def decodeLoadStoreRegister (opc : (BitVec 2)) (Rm : (BitVec 5)) (option_v : (BitVec 3)) (S : (BitVec 1)) (Rn : (BitVec 5)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if (((option_v != 0b011#3) || (S == 1#1)) : Bool)
  then none
  else
    (if ((opc == 0b01#2) : Bool)
    then (some (LoadRegister (t, n, m)))
    else
      (if ((opc == 0b00#2) : Bool)
      then (some (StoreRegister (t, n, m)))
      else none))

def decodeExclusiveOr (sf : (BitVec 1)) (shift : (BitVec 2)) (N : (BitVec 1)) (Rm : (BitVec 5)) (imm6 : (BitVec 6)) (Rn : (BitVec 5)) (Rd : (BitVec 5)) : (Option ast) :=
  let d : reg_index := (BitVec.toNatInt Rd)
  let n : reg_index := (BitVec.toNatInt Rn)
  let m : reg_index := (BitVec.toNatInt Rm)
  if (((sf == 0#1) && ((BitVec.access imm6 5) == 1#1)) : Bool)
  then none
  else
    (if ((imm6 != 0b000000#6) : Bool)
    then none
    else (some (ExclusiveOr (d, n, m))))

def decodeDataMemoryBarrier (merge_var : (BitVec 4)) : (Option ast) :=
  match merge_var with
  | 0b1111 => (some (DataMemoryBarrier MBReqTypes_All))
  | 0b1110 => (some (DataMemoryBarrier MBReqTypes_Writes))
  | 0b1101 => (some (DataMemoryBarrier MBReqTypes_Reads))
  | _ => none

def decodeCompareAndBranch (imm19 : (BitVec 19)) (Rt : (BitVec 5)) : (Option ast) :=
  let t : reg_index := (BitVec.toNatInt Rt)
  let offset : (BitVec 64) := (Sail.BitVec.signExtend (imm19 ++ 0b00#2) 64)
  (some (CompareAndBranch (t, offset)))

/-- Type quantifiers: m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_StoreRegister (t : Nat) (n : Nat) (m : Nat) : SailM Unit := SailME.run do
  let base_addr ← do (rX n)
  let offset ← do (rX m)
  let addr := (base_addr + offset)
  let accdesc := (create_writeAccessDescriptor ())
  let addr ← (( do
    match (translate_address addr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let _ : Unit := (wMem_Addr addr)
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let data ← do (rX t)
  (wMem addr data accdesc)

/-- Type quantifiers: m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_LoadRegister (t : Nat) (n : Nat) (m : Nat) : SailM Unit := SailME.run do
  let base_addr ← do (rX n)
  let offset ← do (rX m)
  let addr := (base_addr + offset)
  let accdesc := (create_readAccessDescriptor ())
  let addr ← (( do
    match (translate_address addr accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let data ← do (rMem addr accdesc)
  (wX t data)

/-- Type quantifiers: m : Nat, n : Nat, d : Nat, 0 ≤ d ∧ d ≤ 31, 0 ≤ n ∧ n ≤ 31, 0 ≤ m
  ∧ m ≤ 31 -/
def execute_ExclusiveOr (d : Nat) (n : Nat) (m : Nat) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  let operand1 ← do (rX n)
  let operand2 ← do (rX m)
  (wX d (operand1 ^^^ operand2))

def execute_DataMemoryBarrier (types : MBReqTypes) : SailM Unit := do
  writeReg _PC (BitVec.addInt (← readReg _PC) 4)
  (dataMemoryBarrier types)

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_CompareAndBranch (t : Nat) (offset : (BitVec 64)) : SailM Unit := do
  let operand ← do (rX t)
  if ((operand == 0x0000000000000000#64) : Bool)
  then
    (do
      let base ← do (rPC ())
      let addr := (base + offset)
      (wPC addr))
  else writeReg _PC (BitVec.addInt (← readReg _PC) 4)

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .LoadRegister (t, n, m) => (execute_LoadRegister t n m)
  | .StoreRegister (t, n, m) => (execute_StoreRegister t n m)
  | .ExclusiveOr (d, n, m) => (execute_ExclusiveOr d n m)
  | .DataMemoryBarrier types => (execute_DataMemoryBarrier types)
  | .CompareAndBranch (t, offset) => (execute_CompareAndBranch t offset)

def decode (v__0 : (BitVec 32)) : (Option ast) :=
  if ((((Sail.BitVec.extractLsb v__0 31 24) == (0xF8#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb
             v__0 21 21) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 11 10) == (0b10#2 : (BitVec 2))))) : Bool)
  then
    (let S := (BitVec.access v__0 12)
    let option_v : (BitVec 3) := (Sail.BitVec.extractLsb v__0 15 13)
    let opc : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
    let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
    let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
    let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
    (decodeLoadStoreRegister opc Rm option_v S Rn Rt))
  else
    (if (((Sail.BitVec.extractLsb v__0 30 24) == (0b1001010#7 : (BitVec 7))) : Bool)
    then
      (let sf := (BitVec.access v__0 31)
      let N := (BitVec.access v__0 21)
      let shift : (BitVec 2) := (Sail.BitVec.extractLsb v__0 23 22)
      let imm6 : (BitVec 6) := (Sail.BitVec.extractLsb v__0 15 10)
      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
      let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
      let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
      (decodeExclusiveOr sf shift N Rm imm6 Rn Rd))
    else
      (if ((((Sail.BitVec.extractLsb v__0 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb
               v__0 7 0) == (0xBF#8 : (BitVec 8)))) : Bool)
      then
        (let CRm : (BitVec 4) := (Sail.BitVec.extractLsb v__0 11 8)
        (decodeDataMemoryBarrier CRm))
      else
        (if (((Sail.BitVec.extractLsb v__0 31 24) == (0xB4#8 : (BitVec 8))) : Bool)
        then
          (let imm19 : (BitVec 19) := (Sail.BitVec.extractLsb v__0 23 5)
          let Rt : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
          (decodeCompareAndBranch imm19 Rt))
        else none)))

def fetch_and_execute (_ : Unit) : SailM Unit := SailME.run do
  let accdesc := (create_iFetchAccessDescriptor ())
  let addr ← (( do
    match (translate_address (← readReg _PC) accdesc) with
    | .some addr => (pure addr)
    | none => SailME.throw (() : Unit) ) : SailME Unit (BitVec addr_size) )
  let machineCode ← do (iFetch addr accdesc)
  let instr := (decode machineCode)
  match instr with
  | .some instr => (execute instr)
  | none => assert false "Unsupported Encoding"


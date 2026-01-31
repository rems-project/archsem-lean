import Out.Sail.Attr

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

import Out.Sail.ArchSem

namespace Sail

namespace BitVec

abbrev length {w : Nat} (_ : BitVec w) : Nat := w

@[simp_sail]
def toNatInt {w : Nat} (x : BitVec w) : Int :=
  Int.ofNat x.toNat

@[simp_sail]
def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.signExtend w'

@[simp_sail]
def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.zeroExtend w'

@[simp_sail]
def truncate {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.truncate w'

@[simp_sail]
def truncateLsb {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.extractLsb' (w - w') w'

@[simp_sail]
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

@[simp_sail]
def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := ((y.zeroExtend w) <<< start)
  (mask &&& x) ||| y'

@[simp_sail]
def slice {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' start len

@[simp_sail]
def sliceBE {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' (w - start - len) len

@[simp_sail]
def subrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb' (w - hi - 1) _

@[simp_sail]
def updateSubrange {w : Nat} (x : BitVec w) (hi lo : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x lo _ y

@[simp_sail]
def updateSubrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x (w - hi - 1) _ y

@[simp_sail]
def replicateBits {w : Nat} (x : BitVec w) (i : Nat) := BitVec.replicate i x

@[simp_sail]
def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[i]!

@[simp_sail]
def accessBE {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[w - i - 1]!

@[simp_sail]
def addInt {w : Nat} (x : BitVec w) (i : Int) : BitVec w :=
  x + BitVec.ofInt w i

@[simp_sail]
def subInt (x : BitVec w) (i : Int) : BitVec w :=
  x - BitVec.ofInt w i

@[simp_sail]
def countLeadingZeros (x : BitVec w) : Nat := x.clz.toNat

@[simp_sail]
def countTrailingZeros (x : BitVec w) : Nat :=
  countLeadingZeros (x.reverse)

@[simp_sail]
def append' (x : BitVec n) (y : BitVec m) {mn}
    (hmn : mn = n + m := by (conv => rhs; simp); try rfl) : BitVec mn :=
  (x.append y).cast hmn.symm

@[simp_sail]
def update (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x n _ b

@[simp_sail]
def updateBE (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x (m - n - 1) _ b

def toBin {w : Nat} (x : BitVec w) : String :=
  String.ofList (List.map (fun c => if c then '1' else '0') (List.ofFn (BitVec.getMsb x)))

def toFormatted {w : Nat} (x : BitVec w) : String :=
  if (length x % 4) == 0 then
    s!"0x{String.toUpper (BitVec.toHex x)}"
  else
    s!"0b{BitVec.toBin x}"

@[simp_sail]
def join1 (xs : List (BitVec 1)) : BitVec xs.length :=
  (BitVec.ofBoolListBE (xs.map fun x => x[0])).cast (by simp)

instance (priority := low) : Coe (BitVec (1 * n)) (BitVec n) where
  coe x := x.cast (by simp)

end BitVec

def charToHex (c : Char) : BitVec 4 :=
  match c.toLower with
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | 'a' => 10 | 'b' => 11 | 'c' => 12 | 'd' => 13
  | 'e' => 14 | 'f' => 15 | _ => 0

def round4 (n : Nat) := ((n - 1) / 4) * 4 + 4

def parse_hex_bits_digits (n : Nat) (str : String) : BitVec n :=
  let len := str.length
  if h : n < 4 || len = 0 then BitVec.zero n else
    let bv := parse_hex_bits_digits (n-4) (str.take (len-1))
    let c := String.Pos.Raw.get! str ⟨len-1⟩ |> charToHex
    BitVec.append bv c |>.cast (by simp_all)
decreasing_by simp_all <;> omega

def parse_dec_bits (n : Nat) (str : String) : BitVec n :=
  go str.length str
where
  -- TODO: when there are lemmas about `String.take`, replace with WF induction
  go (fuel : Nat) (str : String) :=
    if fuel = 0 then 0 else
      let lsd := String.Pos.Raw.get! str ⟨str.length - 1⟩
      let rest := str.take (str.length - 1)
      (charToHex lsd).setWidth n + 10#n * go (fuel-1) rest

def parse_hex_bits (n : Nat) (str : String) : BitVec n :=
  let bv := parse_hex_bits_digits (round4 n) (str.drop 2)
  bv.setWidth n

def valid_hex_bits (n : Nat) (str : String) : Bool :=
  if str.length < 2 then false else
  let str := str.drop 2
  str.all fun x => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'] &&
  2 ^ n > (parse_hex_bits_digits (round4 n) str).toNat

def valid_dec_bits (_ : Nat) (str : String) : Bool :=
  str.all fun x => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

@[simp_sail]
def shift_bits_left (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv <<< sh

@[simp_sail]
def shift_bits_right (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv >>> sh

@[simp_sail]
def shiftl (bv : BitVec n) (m : Nat) : BitVec n :=
  bv <<< m

@[simp_sail]
def shiftr (bv : BitVec n) (m : Nat) : BitVec n :=
  bv >>> m

@[simp_sail]
def pow2 := (2 ^ ·)

namespace Nat

-- NB: below is taken from Mathlib.Logic.Function.Iterate
/-- Iterate a function. -/
def iterate {α : Sort u} (op : α → α) : Nat → α → α
  | 0, a => a
  | Nat.succ k, a => iterate op k (op a)

def toHex (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex

def toHexUpper (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex.toUpper

end Nat

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

@[simp_sail]
def shiftl (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x * 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x / 2) (n+1) a

@[simp_sail]
def shiftr (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x / 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x * 2) (n+1) a


def toHex (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHex n
  | Int.negSucc n => "-" ++ Nat.toHex (n+1)

def toHexUpper (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHexUpper n
  | Int.negSucc n => "-" ++ Nat.toHexUpper (n+1)

end Int

@[simp_sail]
def get_slice_int (len : Nat) (n : Int) (lo : Nat) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)

@[simp_sail]
def set_slice_int (len : Nat) (n : Int) (lo : Nat) (x : BitVec len) : Int :=
  BitVec.toInt (BitVec.updateSubrange' (BitVec.ofInt len n) lo len x)

@[simp_sail]
def set_slice {n : Nat} (m : Nat) (bv : BitVec n) (start : Nat) (bv' : BitVec m) : BitVec n :=
  BitVec.updateSubrange' bv start m bv'

def String.leadingSpaces (s : String) : Nat :=
  s.length - (s.dropWhile (· = ' ')).length

abbrev Vector.length (_v : Vector α n) : Nat := n

@[simp_sail]
def vectorInit {n : Nat} (a : α) : Vector α n := Vector.replicate n a

@[simp_sail]
def vectorUpdate (v : Vector α m) (n : Nat) (a : α) := v.set! n a

@[simp_sail]
instance : HShiftLeft (BitVec w) Int (BitVec w) where
  hShiftLeft b i :=
    match i with
    | .ofNat n => BitVec.shiftLeft b n
    | .negSucc n => BitVec.ushiftRight b (n + 1)

@[simp_sail]
instance : HShiftRight (BitVec w) Int (BitVec w) where
  hShiftRight b i := b <<< (- i)

section PreSailTypes

open ArchSem

structure ChoiceSource where
  (α : Type)
  (nextState : Primitive → α → α)
  (choose : ∀ p : Primitive, α → Primitive.reflect p)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

/-
class ConcurrencyInterfaceV1.Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

class ConcurrencyInterfaceV2.Arch where
  addr_size : Nat
  addr_space : Type
  CHERI : Bool
  cap_size_log : Nat

  mem_acc : Type
  mem_acc_is_explicit : mem_acc -> Bool
  mem_acc_is_ifetch : mem_acc -> Bool
  mem_acc_is_ttw : mem_acc -> Bool
  mem_acc_is_relaxed : mem_acc -> Bool
  mem_acc_is_rel_acq_rcpc : mem_acc -> Bool
  mem_acc_is_rel_acq_rcsc : mem_acc -> Bool
  mem_acc_is_standalone : mem_acc -> Bool
  mem_acc_is_exclusive : mem_acc -> Bool
  mem_acc_is_atomic_rmw : mem_acc -> Bool

  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlbi : Type
  exn : Type
  sys_reg_id : Type /- CR clang: this is reg_acc in rocq archsem -/
-/

end PreSailTypes

def print_int : String → Int → Unit := fun _ _ => ()

def prerr_int : String → Int → Unit := fun _ _ => ()

def prerr_bits: String → BitVec n → Unit := fun _ _ => ()

def print_endline : String → Unit := fun _  => ()

def prerr_endline : String → Unit := fun _ => ()

def print : String → Unit := fun _ => ()

def prerr : String → Unit := fun _ => ()

/- CR clang: Ahh, this is ugly. But this is how it is in sail. -/
/- NOTE :todo conversion ; todo ArchSem namespace ; & other isolation (archsem, sail files & lean conventions) -/
namespace ConcurrencyInterfaceV2
open ArchSem
variable [Arch]
structure Mem_request (size : Nat) (num_tag : Nat) (addr_size : Nat) (addr_space : Type) (mem_acc : Type) where
  access_kind : mem_acc
  address : BitVec addr_size
  address_space : addr_space
  size : {n : Nat // n = size}
  num_tag : {n : Nat // n = num_tag}
/- CR clang: this is just to make the above tolerable. -/
abbrev Arch_mem_request size num_tag := Mem_request size num_tag Arch.addr_size Arch.addr_space Arch.mem_acc
end ConcurrencyInterfaceV2

end Sail

namespace PreSail

open Sail

section Interface

open ArchSem
variable [Arch]

/- CR chris: what is this for? -/
inductive RegisterRef : Type → Type where
  | Reg (r : Arch.register) : RegisterRef (Arch.register_type r)
export RegisterRef (Reg)

inductive SailEffectError (userError : Type) where
  | GenericError (err : GenericError)
  | UserError (err : userError)

  /-
abbrev PreSailM (RegisterType : Register → Type) (c : ChoiceSource) (ue: Type) :=
  EStateM (Error ue) (SequentialState RegisterType c)
  -/
/- CR clang: make the sum type an inductive. -/
abbrev PreSailM (userError : Type) := FreeM (Result InstructionEffect (SailEffectError userError))
  (fun | .Ok eff => eff.ret | .Err _ => Empty)

@[simp_sail]
def sailTryCatch (e : PreSailM ue α) (h : ue → PreSailM ue α) : PreSailM ue α :=
  match e with
  | .pure a => .pure a
  | .bind (.Err (.UserError e)) _k => h e
  | .bind eff k => .bind eff (fun r => sailTryCatch (k r) h)

@[simp_sail]
def sailThrow (e : ue) : PreSailM ue α :=
    FreeM.bind (.Err (.UserError e)) Empty.elim

/- CR clang: TODO implement this -/
instance: MonadExceptOf (SailEffectError userError) (PreSailM userError) where
  throw e := FreeM.bind (.Err e) Empty.elim
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)

def choose (p : Primitive) : PreSailM ue p.reflect :=
  FreeM.bind (.Ok (InstructionEffect.Choice p)) FreeM.pure

def undefined_unit (_ : Unit) : PreSailM ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM ue (BitVec 1) :=
  choose .bit

def undefined_bool (_ : Unit) : PreSailM ue Bool :=
  choose .bool

def undefined_int (_ : Unit) : PreSailM ue Int :=
  choose .int

def undefined_range (low high : Int) : PreSailM ue Int := do
  pure (low + (← choose .int) % (high - low))

def undefined_nat (_ : Unit) : PreSailM ue Nat :=
  choose .nat

def undefined_string (_ : Unit) : PreSailM ue String :=
  choose .string

def undefined_bitvector (n : Nat) : PreSailM ue (BitVec n) :=
  choose <| .bitvector n

def undefined_vector (n : Nat) (a : α) : PreSailM ue (Vector α n) :=
  pure <| .replicate n a

def internal_pick {α : Type} : List α → PreSailM ue α
  | [] => FreeM.bind (.GenericError .Unreachable) Empty.elim
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

@[simp_sail]
def writeReg (r : Arch.register) (v : Arch.register_type r) : PreSailM ue PUnit :=
  FreeM.bind (InstructionEffect.RegWrite r Option.none v) FreeM.pure

@[simp_sail]
def readReg (r : Arch.register) : PreSailM ue (Arch.register_type r) :=
  FreeM.bind (InstructionEffect.RegRead r Option.none) FreeM.pure

@[simp_sail]
def readRegRef (reg_ref : RegisterRef α) : PreSailM ue α := do
  match reg_ref with | .Reg r => readReg r

@[simp_sail]
def writeRegRef (reg_ref : RegisterRef α) (a : α) : PreSailM ue Unit := do
  match reg_ref with | .Reg r => writeReg r a

@[simp_sail]
def reg_deref (reg_ref : RegisterRef α) : PreSailM ue α :=
  readRegRef reg_ref

@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM ue Unit :=
  if p then .pure () else .bind (.GenericError (.Assertion s)) Empty.elim

section ConcurrencyInterface

/- CR chris: I think these aren't used externally so I'm commenting out. We cant implement
  with the new free monad effect system because there are no default mem_acc settings.-/
/-
@[simp_sail]
def writeByte (addr : Nat) (value : BitVec 8) : PreSailM ue Unit := do
  FreeM.bind (InstructionEffect.MemWrite sorry sorry sorry) FreeM.pure

/- CR chris: Why do I keep seeing read and writes returning bools?-/
@[simp_sail]
def writeBytes (addr : Nat) (value : BitVec (8 * n)) : PreSailM ue Bool :=
  FreeM.bind (InstructionEffect.MemWrite sorry sorry sorry) sorry

@[simp_sail]
def writeByteVec (addr : Nat) (value : Vector (BitVec 8) n) : PreSailM ue Bool :=
  sorry

@[simp_sail]
def write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    PreSailM ue Unit := sorry

@[simp_sail]
def readByte (addr : Nat) : PreSailM ue (BitVec 8) :=
  FreeM.bind (InstructionEffect.MemRead sorry) sorry

@[simp_sail]
def readBytes (size : Nat) (addr : Nat) : PreSailM ue (BitVec (8 * size)) :=
  FreeM.bind (InstructionEffect.MemRead sorry) sorry

@[simp_sail]
def readBytesVec (size : Nat) (addr : Nat) :
    PreSailM ue (Vector (BitVec 8) size) :=
  sorry
-/

/-
namespace ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1

@[simp_sail]
def sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result (Option Bool) Arch.abort) := do
  let addr := req.pa.toNat
  let b ← match req.value with
    | some v => writeBytes addr v
    | none => pure true
  pure (Ok (some b))

@[simp_sail]
def sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := do
  let addr := req.pa.toNat
  let value ← readBytes n addr
  pure (Ok value)


@[simp_sail]
def sail_barrier (_ : α) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_cache_op [Arch] (_ : Arch.cache_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_tlbi [Arch] (_ : Arch.tlb_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_start [Arch] (_ : Arch.trans_start) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_end [Arch] (_ : Arch.trans_end) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_take_exception [Arch] (_ : Arch.fault) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_return_exception [Arch] (_ : Arch.pa) : PreSailM RegisterType c ue Unit := pure ()

end ConcurrencyInterfaceV1
-/

namespace ConcurrencyInterfaceV2

open Sail.ConcurrencyInterfaceV2

/- CR clang: put these utility functions somewhere better. -/
def vecbytes_to_bitvec (vec : Vector (BitVec 8) n) : BitVec (8 * n) :=
  vec.foldl (fun (i, acc) x => (i+1, BitVec.updateSubrange' acc n 8 x)) (0, BitVec.zero (8 * n))
  |> Prod.snd
def bitvec_to_vecbytes (bitvec : BitVec (8 * n)) : Vector (BitVec 8) n :=
  Vector.ofFn (fun i => BitVec.slice bitvec (8 * i) 8)
def vecbool_to_bitvec (vec : Vector Bool n) : BitVec n :=
  vec.foldl (fun (i, acc) b => (i+1, BitVec.updateSubrange' acc n 1 (BitVec.ofBool b))) (0, BitVec.zero n)
  |> Prod.snd
def bitvec_to_vecbool (bitvec : BitVec n) : Vector Bool n :=
  Vector.ofFn (fun i => BitVec.getLsb bitvec i)

def sail_mem_requset_to_archsem (mem_req : Arch_mem_request size num_tag) : ArchSem.MemRequest :=
    { accessKind := mem_req.access_kind
    , address := mem_req.address
    , addressSpace := mem_req.address_space
    , size := mem_req.size
    , numTag := mem_req.num_tag }
  /-
  if mem_req.size = size ∧ mem_req.num_tag = num_tag then
  else
    /- CR clang: better error message? -/
    /- panic! "INTERNAL ERROR: inconsistent memory request structure" -/
    /- CR clang: actually how do I even error out here? MemRequest needs to be inhabited? -/
    sorry
  -/

@[simp_sail]
def sail_mem_read (mem_req : Arch_mem_request size num_tag) :
    PreSailM ue (Result ((Vector (BitVec 8) size) × Vector Bool num_tag) Arch.abort) :=
  let req := sail_mem_requset_to_archsem mem_req
  /- CR clang: there must be a cleaner way to write this -/
  have h : (req.size = size) ∧ (req.numTag = num_tag) := by
    simp [req, sail_mem_requset_to_archsem]
    simp [mem_req.size.property, mem_req.num_tag.property]
  FreeM.bind (InstructionEffect.MemRead req)
    (FreeM.pure ∘ Result.map (fun (bytes,tags) =>
      (bitvec_to_vecbytes (And.left h ▸ bytes), bitvec_to_vecbool (And.right h ▸ tags))))
    /-
    (FreeM.pure ∘ (Result.map (Prod.map bitvec_to_vecbytes bitvec_to_vecbool)))
    -/

def sail_mem_write (mem_req : Arch_mem_request size num_tag) (value : Vector (BitVec 8) size) (tags : Vector Bool num_tag) :
    PreSailM ue (Result Unit Arch.abort) :=
  let req := sail_mem_requset_to_archsem mem_req
  have h : (req.size = size) ∧ (req.numTag = num_tag) := by
    simp [req, sail_mem_requset_to_archsem]
    simp [mem_req.size.property, mem_req.num_tag.property]
  FreeM.bind (InstructionEffect.MemWrite req
    (vecbytes_to_bitvec (And.left h ▸ value)) (vecbool_to_bitvec (And.right h ▸ tags))) FreeM.pure

/- CR clang: why do we have this RegisterRef type? -/
@[simp_sail]
def sail_sys_reg_write (id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : PreSailM ue PUnit :=
  let (Reg r) := r
  FreeM.bind (InstructionEffect.RegWrite r (.some id) v) FreeM.pure

@[simp_sail]
def sail_sys_reg_read (id : Arch.sys_reg_id) (r : RegisterRef α) : PreSailM ue α :=
  let (Reg r) := r
  FreeM.bind (InstructionEffect.RegRead r (.some id)) FreeM.pure

/-
@[simp_sail]
def sail_sys_reg_read (_id : Arch.sys_reg_id) (r : @RegisterRef Register RegisterType α) : PreSailM ue RegisterType c ue α :=
  readRegRef r

@[simp_sail]
def sail_sys_reg_write [Arch] (_id : Arch.sys_reg_id) (r : @RegisterRef Register RegisterType α) (v : α) :
    PreSailM ue RegisterType c ue Unit :=
  writeRegRef r v
-/

def sail_mem_address_announce (mem_req : Arch_mem_request size num_tag) : PreSailM ue Unit :=
  let req := sail_mem_requset_to_archsem mem_req
  FreeM.bind (InstructionEffect.MemWriteAnnounce req) FreeM.pure

@[simp_sail]
def sail_translation_start (ts : Arch.trans_start) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.TranslationStart ts) FreeM.pure

@[simp_sail]
def sail_translation_end (te : Arch.trans_end) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.TranslationEnd te) FreeM.pure

@[simp_sail]
def sail_barrier (b : Arch.barrier) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.Barrier b) FreeM.pure

/- CR clang: implement these together with the other exception stuff. -/
@[simp_sail]
def sail_take_exception (e : Arch.exn) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.ArchException e) FreeM.pure
  
@[simp_sail]
def sail_return_exception (_ : Unit) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.ReturnExecption) FreeM.pure

@[simp_sail]
def sail_cache_op (op : Arch.cache_op) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.CacheOp op) FreeM.pure

@[simp_sail]
def sail_tlbi (op : Arch.tlbi) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.TlbOp op) FreeM.pure

end ConcurrencyInterfaceV2

/- CR clang: I'm hoping this isnt used since we cant implement... -/
/-
@[simp_sail]
def read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : PreSailM RegisterType c ue (BitVec (8 * data_size)) := do
  let ⟨bytes, _⟩ ← readBytes data_size addr.toNat
  pure bytes
-/

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM ue Unit := FreeM.bind (InstructionEffect.ClockCycle) FreeM.pure

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM ue Nat := FreeM.bind (InstructionEffect.GetCycleCount) FreeM.pure

end ConcurrencyInterface

def print_effect (str : String) : PreSailM ue Unit :=
  FreeM.bind (InstructionEffect.PrintMessage str) FreeM.pure

def print_int_effect (str : String) (n : Int) : PreSailM ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM ue Unit :=
  print_effect s!"{str}{BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM ue Unit :=
  print_effect s!"{str}\n"

/- CR clang: maybe this should be in the `section SailME` and be defined on that PreSailME type? -/
/-
@[simp_sail]
def sailTryCatchE (e : ExceptT β PreSailM α) (h : Error Arch.sail_exception → ExceptT β PreSailM α) : ExceptT β PreSailM α :=
  EStateM.tryCatch e fun e =>
    match e with
    | .User u => h u
    | _ => EStateM.throw e
    -/

end Interface

section SailME

open ArchSem
variable [Arch]


inductive SailExceptionInstructionEffect (userError : Type) (exception : Type) where
  | Base (eff : InstructionEffect)
  | GenericError (err : GenericError)
  | UserError (err : userError)
  | Exception (ex : exception)

instance : Coe InstructionEffect (SailExceptionInstructionEffect userError exception) where
  coe eff := .Base eff

def SailExceptionInstructionEffect.ret : SailExceptionInstructionEffect userError exception → Type
  | Base eff => InstructionEffect.ret eff
  | _ => Empty

/-
abbrev PreSailME user_error exception := PreSailM (exception ⊕ GenericError ⊕ user_error)
-/
abbrev PreSailME user_error exception := FreeM (SailExceptionInstructionEffect user_error exception) SailExceptionInstructionEffect.ret

/-
instance: MonadExceptOf (Error ue) (PreSailME ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)
-/

def PreSailME.run (m : PreSailME ue α α) : PreSailM ue α := do
  match m with
  | FreeM.pure v => FreeM.pure v
  | FreeM.bind (.Exception ex) _cont => FreeM.pure ex
  | FreeM.bind (.GenericError err) cont => FreeM.bind (.GenericError err) (fun ret => PreSailME.run (cont ret))
  | FreeM.bind (.UserError err) cont => FreeM.bind (.UserError err) (fun ret => PreSailME.run (cont ret))
  | FreeM.bind (.Base eff) cont => FreeM.bind (.Base eff) (fun ret => PreSailME.run (cont ret))

/-
def _root_.ExceptT.map_error [Monad m] (e : ExceptT ε m α) (f : ε → ε') : ExceptT ε' m α :=
  ExceptT.mk <| do
    match ← e.run with
    | .ok x => pure $ .ok x
    | .error e => pure $ .error (f e)
-/

/-
instance [∀ x, CoeT α x α'] :
    CoeT (PreSailME ue α β) e (PreSailME ue α' β) where
  coe := e.map_error (fun x => match x with | .inl e => .inl e | .inr e => .inr e)
-/

def PreSailME.throw (ex : exception) : PreSailME userError exception α :=
  FreeM.bind (.Exception ex) Empty.elim

/-
instance : Inhabited (PreSail.SequentialState RT trivialChoiceSource) where
  default := ⟨default, (), default, default, default, default⟩
-/

end SailME

end PreSail

/-
abbrev ExceptM α := ExceptT α Id

def ExceptM.run (m : ExceptM α α) : α :=
  match (ExceptT.run m) with
    | .error e => e
    | .ok e => e
-/

namespace Sail

open PreSail

/-
variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]
-/

/- CR clang: So this is going to be put into the free monad interpreter -/
/-
def main_of_sail_main (initialState : SequentialState RegisterType c) (main : Unit → PreSailM Unit) : IO UInt32 := do
  let res := main () |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1
-/

end Sail

/-
def whileFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      if ←cond x then go (←f x) n else pure x
  go init fuel

def untilFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      let x ← f x
      if ←cond x then pure x else go x n
  go init fuel
-/


/-
CR clang: So this is some implicit type conversion helpers.
Why are they here? Lets put them up with the rest of the bitvec stuff.
-/

instance : CoeT Int x Nat where
  coe := x.toNat

instance : CoeT (BitVec n) x (BitVec m) where
  coe := x.setWidth m

instance: CoeT (Vector (BitVec n₁) m) x (Vector (BitVec n₂) m) where
  coe := x.map fun (bv : BitVec n₁) => bv.setWidth n₂

instance {α α' β : Type u} (x : α × β) [CoeT α x.1 α'] : CoeT (α × β) x (α' × β) where
  coe := (x.1, x.2)

instance {α α' β : Type u} (x : β × α) [CoeT α x.2 α'] : CoeT (β × α) x (β × α') where
  coe := (x.1, x.2)

instance {α α' β β' : Type u} (x : α × β) [CoeT α x.1 α'] [CoeT β x.2 β'] : CoeT (α × β) x (α' × β') where
  coe := (x.1, x.2)

instance {α α' : Type u} [∀ x, CoeT α x α'] (xs : List α) : CoeT (List α) xs (List α') where
  coe := List.map (α := α) (β := α') (fun x => x) xs

instance (priority := low) : HAdd (BitVec n) (BitVec m) (BitVec n) where
  hAdd x y := x + y

instance (priority := low) : HSub (BitVec n) (BitVec m) (BitVec n) where
  hSub x y := x - y

instance (priority := low) : HAnd (BitVec n) (BitVec m) (BitVec n) where
  hAnd x y := x &&& y

instance (priority := low) : HOr (BitVec n) (BitVec m) (BitVec n) where
  hOr x y := x ||| y

instance (priority := low) : HXor (BitVec n) (BitVec m) (BitVec n) where
  hXor x y := x ^^^ y

instance [GetElem? coll Nat elem valid] : GetElem? coll Int elem (λ c i ↦ valid c i.toNat) where
  getElem c i h := c[i.toNat]'h
  getElem? c i := c[i.toNat]?

instance : HPow Int Int Int where
  hPow x n := x ^ n.toNat

infixl:65 " +i "   => fun (x y : Int) => x + y
infixl:65 " -i "   => fun (x y : Int) => x - y
infixl:65 " ^i "   => fun (x y : Int) => x ^ y
infixl:65 " *i "   => fun (x y : Int) => x * y

notation:50 x "≤b" y => decide (x ≤ y)
notation:50 x "<b" y => decide (x < y)
notation:50 x "≥b" y => decide (x ≥ y)
notation:50 x ">b" y => decide (x > y)

-- for termination measures, since they're almost always `Int`s but not always
abbrev Nat.toNat (x : Nat) := x

set_option grind.warning false
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)

-- This lemma replaces `bif` by `if` in functions when Lean is trying to prove
-- termination.
@[wf_preprocess]
theorem cond_eq_ite (b : Bool) (x y : α) : cond b x y = ite b x y := by cases b <;> rfl


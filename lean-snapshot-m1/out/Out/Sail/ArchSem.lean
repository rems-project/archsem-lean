namespace ArchSem

/- Why not use a lean built-in type? -/
inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

def Result.map (f: α → β) (r : Result α ε) : Result β ε := match r with
| Result.Ok v => Result.Ok (f v)
| Result.Err e => Result.Err e

/- CR chris: Find better name from FreeM.bind. rocq-archsem uses ret and next. maybe `impure` -/
inductive FreeM.{u, v, w} (Eff : Type v) (eff_ret : Eff → Type u) (α : Type w) where
  | pure (a : α) : FreeM Eff eff_ret α
  | bind (call : Eff) (cont : eff_ret call → FreeM Eff eff_ret α) : FreeM Eff eff_ret α

/- CR chris: Namespace this function into FreeM -/
def free_monad_bind (x : FreeM Eff effRet α) (f : α → FreeM Eff effRet β) : FreeM Eff effRet β :=
  match x with
    | FreeM.pure x => f x
    | FreeM.bind op cont => FreeM.bind op (fun r => free_monad_bind (cont r) f)

instance : Monad (FreeM Eff effRet) where
  pure x := FreeM.pure x
  bind := free_monad_bind

inductive Primitive where
  | bool
  | bit
  | int
  | nat
  | string
  | fin (n : Nat)
  | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | bool => Bool
  | bit => BitVec 1
  | int => Int
  | nat => Nat
  | string => String
  | fin n => Fin (n + 1)
  | bitvector n => BitVec n

inductive GenericError where
  | Exit
  | Unreachable
  | OutOfMemoryRange (n : Nat)
  | Assertion (s : String)

def GenericError.print : GenericError → String
  | Exit => "Exit"
  | Unreachable => "Unreachable"
  | OutOfMemoryRange n => s!"{n} Out of Memory Range"
  | Assertion s => s!"Assertion failed: {s}"

/- CR clang: I would like to use lean naming convention but this conflicts with sail. -/
class Arch where
  register : Type
  register_type : register → Type
  sys_reg_id : Type
  
  addr_size : Nat
  addr_space : Type
  mem_acc : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlbi : Type
  trans_start : Type
  trans_end : Type
  
  exn : Type

variable [Arch]

structure MemRequest where
  accessKind : Arch.mem_acc
  address : BitVec Arch.addr_size
  addressSpace : Arch.addr_space
  size : Nat
  numTag : Nat

/- CR clang: See rocq-lean effects in ArchSem/Interface.v `outcome` -/
/- CR clang: After discussion with Thibaut on Mon 26th Jan: We are going to make
this inductive type take an `Error : type` argument. Then this will be instantiated
something like :
  PreSailM : FrMon (outcome arch (generic_error + user_error))
  PreArchM : FreeMon (outcome (generic_error))
  PreSailME : Free Mon(outcome (generic error + user error + A:type))
-/
inductive InstructionEffect where
  | RegRead (reg : Arch.register) (accessType : Option Arch.sys_reg_id)
  | RegWrite (reg : Arch.register) (accessType : Option Arch.sys_reg_id) (value: Arch.register_type reg)
  | MemRead (memReq : MemRequest)
  | MemWrite (memReq : MemRequest) (value : BitVec (8 * memReq.size)) (tags : BitVec (memReq.numTag))
  | MemWriteAnnounce (memReq : MemRequest)
  | Barrier (barrier : Arch.barrier)
  | CacheOp (op : Arch.cache_op)
  | TlbOp (op : Arch.tlbi)
  | Choice (primitive : Primitive)
  | ClockCycle
  | GetCycleCount
  | TranslationStart (translationStart : Arch.trans_start)
  | TranslationEnd (translationEnd : Arch.trans_end)
  | ArchException (exception : Arch.exn)
  | ReturnExecption
  /- CR clang: Maybe split this out into different types: -/
  | PrintMessage (msg : String)

/- CR clang: namespcae this -/
def InstructionEffect.ret : InstructionEffect → Type
  | .RegRead reg _ => Arch.register_type reg
  | .RegWrite _ _ _ => Unit
  | .MemRead memReq => Result (BitVec (8 * memReq.size) × BitVec (memReq.numTag)) Arch.abort
  | .MemWrite _ _ _ => Result Unit Arch.abort
  | .MemWriteAnnounce _ => Unit
  | .Barrier _ => Unit
  | .CacheOp _ => Unit
  | .TlbOp _ => Unit
  | .Choice primitive => primitive.reflect
  | .ClockCycle => Unit
  | .GetCycleCount => Nat
  | .TranslationStart _ => Unit
  | .TranslationEnd _ => Unit
  | .ArchException _ => Unit
  | .ReturnExecption => Unit
  | .PrintMessage _ => Unit

end ArchSem

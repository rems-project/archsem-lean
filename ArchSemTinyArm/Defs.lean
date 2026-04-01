import Sail
import Out.Defs
import Out.TinyArm
import ArchSem.Common

open Sail.ArchSem

namespace ArchSemTinyArm

instance : Repr Arch.addr_space := by
  conv => rhs ; whnf
  infer_instance

def registerOfString : String → Except String Arch.register
  | "R0" => .ok .R0
  | "R1" => .ok .R1
  | "R2" => .ok .R2
  | "R3" => .ok .R3
  | "R4" => .ok .R4
  | "R5" => .ok .R5
  | "R6" => .ok .R6
  | "R7" => .ok .R7
  | "R8" => .ok .R8
  | "R9" => .ok .R9
  | "R10" => .ok .R10
  | "R11" => .ok .R11
  | "R12" => .ok .R12
  | "R13" => .ok .R13
  | "R14" => .ok .R14
  | "R15" => .ok .R15
  | "R16" => .ok .R16
  | "R17" => .ok .R17
  | "R18" => .ok .R18
  | "R19" => .ok .R19
  | "R20" => .ok .R20
  | "R21" => .ok .R21
  | "R22" => .ok .R22
  | "R23" => .ok .R23
  | "R24" => .ok .R24
  | "R25" => .ok .R25
  | "R26" => .ok .R26
  | "R27" => .ok .R27
  | "R28" => .ok .R28
  | "R29" => .ok .R29
  | "R30" => .ok .R30
  | "_PC" => .ok ._PC
  | s => .error s!"Invalid register name '{s}'"

/--- Used to define the register total order. -/
private def regNum : Arch.register → Int
  | ._PC => -1
  | .R0 => 1
  | .R1 => 2
  | .R2 => 3
  | .R3 => 4
  | .R4 => 5
  | .R5 => 6
  | .R6 => 7
  | .R7 => 8
  | .R8 => 9
  | .R9 => 10
  | .R10 => 11
  | .R11 => 12
  | .R12 => 13
  | .R13 => 14
  | .R14 => 15
  | .R15 => 16
  | .R16 => 17
  | .R17 => 18
  | .R18 => 19
  | .R19 => 20
  | .R20 => 21
  | .R21 => 22
  | .R22 => 23
  | .R23 => 24
  | .R24 => 25
  | .R25 => 26
  | .R26 => 27
  | .R27 => 28
  | .R28 => 29
  | .R29 => 30
  | .R30 => 31

theorem regNum_injective : Function.Injective regNum := by
  simp [Function.Injective]
  intro x y
  intros
  cases x <;> cases y <;> first
    | contradiction
    | rfl

instance : Ord (Arch.register) where
  compare := compareOn regNum

instance : Std.TransCmp (Ord.compare : Arch.register → Arch.register → Ordering) := by
  simpa [compareOn, regNum] using (inferInstance : Std.TransCmp (compareOn regNum))

instance : Std.LawfulEqCmp (Ord.compare : Arch.register → Arch.register → Ordering) where
  eq_of_compare := by
    intro a b h
    simp [compare, compareOn, compareOfLessAndEq] at *
    split at h <;> try split at h
    all_goals try contradiction
    rename_i eq
    exact regNum_injective eq

def registerTypeOfGen (reg : Arch.register)
    : RegValGen → Except String (Arch.register_type reg)
  | .number n => do
    if n < 0 then Except.error "Register values must be positive"
    if n >= 2^64 then Except.error s!"Register value too large to fit in 64 bit word: {n}"
    -- All register types are `BitVec 64` at the moment.
    let h : Arch.register_type reg = BitVec 64 := by
      simp [Arch.register_type, RegisterType]
      split <;> rfl
    pure (h ▸ BitVec.ofNat 64 n)
  | _ => .error "Register value must be number"

instance : ArchExtra := by
  -- Split the goal into ArchExtra fields.
  refine'
    { register_of_string := registerOfString
    , register_type_of_gen := registerTypeOfGen
    , .. }
  -- Solve trivial cases
  all_goals try infer_instance
  -- Solve the easy cases of the form `TypeClass α`.
  all_goals
    try
    (conv => rhs ; whnf)
    infer_instance
  -- Solve the cases parameterized by Arch.register.
  all_goals
    try
    intro
    (conv => rhs ; whnf)
    split <;> infer_instance

def sailTinyArmIsem := Out.Functions.fetch_and_execute ()

end ArchSemTinyArm

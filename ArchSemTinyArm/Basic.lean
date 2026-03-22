import Sail
import Out.Defs
import Out.TinyArm
import ArchsemLean.Common

open Sail.ArchSem

instance : Repr Arch.addr_space := by
  conv => rhs ; whnf
  infer_instance

instance : ArchExtra := by
  -- Split the goal into ArchExtra fields.
  refine' { .. }
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

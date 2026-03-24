import ArchSem.LitmusTest.Basic
import ArchSem.TerminatingModel
import Sail.ArchSem

open ArchSem.TerminatingModel
open Sail.ArchSem

namespace ArchSem.LitmusTest.Run

structure ArchTestRepr [ArchExtra] (nThreads : Nat) where
  initialState : ArchState nThreads
  terminationCondition : TerminationCondition nThreads
  checkFinalConditions : ArchState nThreads → Except String Unit

def ArchTestRepr.ofTestRepr [ArchExtra] (test : TestRepr)
    : Except String (ArchTestRepr test.registers.length) := do
  -- Helper function.
  let tableToRegMap (l : List (String × RegValGen)) : Except String RegisterMap :=
    l.foldlM (fun regs (s, rv) => do
      let reg : Arch.register ← ArchExtra.register_of_string s
      let val : Arch.register_type reg ← ArchExtra.register_type_of_gen reg rv
      pure (regs.insert reg val)
    ) RegisterMap.empty

  -- Convert TestRepr lists into Vectors of same length.
  let nThreads : Nat := test.registers.length
  let testRegsVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨test.registers.toArray, rfl⟩
  if h : test.termCond.length != nThreads then
    Except.error "A termination condition must be supplied for every thread" else
  let testTermCondVec : Vector (List (String × RegValGen)) nThreads :=
    ⟨test.termCond.toArray, by simp at h ; exact h⟩

  -- Convert to ArchState types.
  let memory : MemoryMap := test.memory.foldl MemoryBlock.insertIntoMemoryMap MemoryMap.empty
  let addressSpace : Arch.addr_space := default
  let regs : Vector RegisterMap nThreads ← testRegsVec.mapM tableToRegMap
  let initialState : ArchState nThreads := { memory, addressSpace, regs}

  -- Convert termination condition.
  let termCondRegs : Vector RegisterMap nThreads ← testTermCondVec.mapM tableToRegMap
  let terminationCondition : TerminationCondition nThreads :=
    fun tid regs => termCondRegs[tid].all (fun r v => regs.get? r == some v)

  -- Convert final condition check.
  let checkFinalMemoryCondition (archState : ArchState nThreads) (cond : FinalMemoryCondition)
      : Except String Unit :=
    let addr : Address := BitVec.ofNat Arch.addr_size cond.addr
    let word : BitVec (8 * cond.size) := archState.memory.read cond.size addr
    match cond.condition with
    | .memEq n => if word.toNat == n then Except.ok () else
      Except.error s!"Expecting '{n}' at '{addr.toHex}', found {word.toNat}"
    | .memNe n => if word.toNat != n then Except.ok () else
      Except.error s!"Final state has '{n}' at '{addr.toHex}'"
  let checkFinalThreadRegisterCondition (archState : ArchState nThreads) (tid : Tid)
      (pair : String × FinalRegisterCondition) := do
    let (reg,cond) := pair
    if h : tid >= nThreads then Except.error s!"Tid out of range {tid}" else
    let tid : Fin nThreads := ⟨tid, by simp at h ; exact h⟩
    let reg : Arch.register ← ArchExtra.register_of_string reg
    let val : Arch.register_type reg ← match cond with
      | .regEq rv | .regNe rv => ArchExtra.register_type_of_gen reg rv
    let trueVal : Arch.register_type reg ← match archState.regs[tid].get? reg with
      | .some val => pure val
      | .none => Except.error s!"Register {reprStr reg} not set in final thread {tid}"
    match cond with
      | .regEq _ => if val == trueVal then pure () else
        Except.error s!"Expecting '{reprStr val}' in {tid}:{reprStr reg}, found '{reprStr trueVal}'"
      | .regNe _ => if val != trueVal then pure () else
        Except.error s!"Final state has '{reprStr val}' in {tid}:{reprStr reg}"
  let checkFinalThreadCondition (archState : ArchState nThreads) (cond : FinalThreadCondition)
      : Except String Unit :=
    cond.regConditions.forM (checkFinalThreadRegisterCondition archState cond.tid)
  let checkFinalCondition (archState : ArchState nThreads) : FinalCondition → Except String Unit
    | .Observable threadConditions memoryConditions
    | .Unobservable threadConditions memoryConditions => do
      threadConditions.forM (checkFinalThreadCondition archState)
      memoryConditions.forM (checkFinalMemoryCondition archState)
  let checkFinalConditions (archState : ArchState nThreads)
      : Except String Unit :=
    test.finalConditions.forM (checkFinalCondition archState)

  -- Return ArchTestRepr.
  pure { initialState, terminationCondition, checkFinalConditions}


-- CR clang: TODO if a test fails we still want all the outputs.
def runLitmusTest [ArchExtra] [DecidableEq Flag] [Repr Flag]
    (litmusTest : TestRepr) (model : ComputationalTerminatingModel Flag)
    : Except String Unit := do
  let nThreads : Nat := litmusTest.registers.length
  let archTest : ArchTestRepr nThreads ← ArchTestRepr.ofTestRepr litmusTest
  let output := model archTest.terminationCondition archTest.initialState
  output.forM (fun
    | .finalState archState _ => archTest.checkFinalConditions archState
    | .flagged f => Except.error s!"Flagged final state {reprStr f}"
    | .error msg => Except.error msg
  )

end ArchSem.LitmusTest.Run

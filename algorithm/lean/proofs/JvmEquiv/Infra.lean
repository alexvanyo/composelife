/-
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 -/

import Lean
import Jvm.Proofs
import Jvm.Tactics
import JvmSemantics
import proofs.MacroCellEngineProofs
import proofs.HashLifeKernelProofs
import proofs.SemanticModelProofs

namespace Algorithm.JvmVerification

instance : Jvm.HasDefaultIsZero algHooks := ⟨rfl⟩

/-! ### Execution helpers -/

export Jvm (
  isBranchInstr BlockChunkRes BlockResChunkRes
  signExtend_and_mask coerceInI32_of_le compareUnsigned_slt' compareUnsigned_sle'
)

@[inline] def stepListAt (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.stepListAt algHooks pc instrs st

@[inline] def stepListAtClean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.stepListAtClean algHooks pc instrs st

def runJvmResFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    Option (JvmVal × JvmState) :=
  Jvm.runJvmResFast algHooks fuel prog pc instrs st

def runJvmValFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    Option JvmVal :=
  Jvm.runJvmValFast algHooks fuel prog pc instrs st

def stepBlockChunk (n : Nat) (fuel : Nat) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    BlockChunkRes AlgExt AlgHeap :=
  Jvm.stepBlockChunk algHooks n fuel pc instrs st

def afterBlockChunk (r : BlockChunkRes AlgExt AlgHeap) (prog : List JvmInstr) : Option JvmVal :=
  Jvm.afterBlockChunk algHooks r prog

def evalBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.evalBranchInstrCons algHooks fuel1 prog pc instr rest st

def stepResBlockChunk (n : Nat) (fuel : Nat) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    BlockResChunkRes AlgExt AlgHeap :=
  Jvm.stepResBlockChunk algHooks n fuel pc instrs st

def afterResBlockChunk (r : BlockResChunkRes AlgExt AlgHeap) (prog : List JvmInstr) :
    Option (JvmVal × JvmState) :=
  Jvm.afterResBlockChunk algHooks r prog

def evalResBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.evalResBranchInstrCons algHooks fuel1 prog pc instr rest st

theorem runJvm_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvm (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res := by
  dsimp only [runJvm, stepInstr]
  rw [Jvm.runJvm_nonbranch algHooks fuel prog st instr hget hnbr]
  cases Jvm.stepInstr algHooks instr st with
  | inl o => cases o <;> rfl
  | inr res => rfl

theorem runJvm_of_stepListAt (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAt st.pc instrs st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_stepListAt algHooks prog instrs fuel st v hdrop hfuel hstep

theorem stepListAt_of_clean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) (v : JvmVal)
    (h : stepListAtClean pc instrs st = some v) :
    stepListAt pc instrs st = some v :=
  Jvm.stepListAt_of_clean algHooks pc instrs st v h

theorem runJvm_of_stepListAtClean (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAtClean st.pc instrs st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_stepListAtClean algHooks prog instrs fuel st v hdrop hfuel hstep

theorem runJvmRes_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvmRes (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvmRes fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none := by
  dsimp only [runJvmRes, stepInstr]
  rw [Jvm.runJvmRes_nonbranch algHooks fuel prog st instr hget hnbr]
  cases Jvm.stepInstr algHooks instr st with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

private theorem algHooks_iteZero? (v : JvmVal) (t e : Option JvmVal) :
    algHooks.iteZero? v t e =
      match algHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp [algHooks, Jvm.JvmHooks.iteZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x =>
    simp only [Jvm.defaultIteVal_eq_if]
    cases hx : (x == 0) <;> simp [hx]

private theorem algHooks_iteNonZero? (v : JvmVal) (t e : Option JvmVal) :
    algHooks.iteNonZero? v t e =
      match algHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp [algHooks, Jvm.JvmHooks.iteNonZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x =>
    simp only [Jvm.defaultIteVal_eq_if]
    cases hx : (x == 0) <;> simp [hx]

theorem runJvm_eq_runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) :
    runJvm fuel prog st = (runJvmRes fuel prog st).map Prod.fst :=
  Jvm.runJvm_eq_runJvmRes algHooks algHooks_iteZero? algHooks_iteNonZero? fuel prog st

theorem runJvmRes_of_runJvmResFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) (res : JvmVal × JvmState)
    (hpc : st.pc = pc) (hdrop : prog.drop pc = instrs)
    (hfast : runJvmResFast fuel prog pc instrs st = some res) :
    runJvmRes fuel prog st = some res :=
  Jvm.runJvmRes_of_runJvmResFast algHooks fuel prog pc instrs st res hpc hdrop hfast

theorem runJvm_of_runJvmValFast (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hfast : runJvmValFast fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_runJvmValFast algHooks algHooks_iteZero? algHooks_iteNonZero? fuel prog st v hfast

theorem runJvm_of_runJvmValFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hpc : st.pc = 0)
    (hfast : runJvmValFast fuel prog 0 prog st = some v) :
    runJvm fuel prog st = some v :=
  Jvm.runJvm_of_runJvmValFast0 algHooks algHooks_iteZero? algHooks_iteNonZero? fuel prog st v hpc hfast

theorem runJvmRes_of_runJvmResFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState)
    (res : JvmVal × JvmState) (hpc : st.pc = 0)
    (hfast : runJvmResFast fuel prog 0 prog st = some res) :
    runJvmRes fuel prog st = some res :=
  Jvm.runJvmRes_of_runJvmResFast0 algHooks fuel prog st res hpc hfast

theorem runJvmRes_map_of_runJvmResFast0 {α : Type} (f : JvmVal × JvmState → α)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (y : α)
    (hpc : st.pc = 0)
    (hfast : (runJvmResFast fuel prog 0 prog st).map f = some y) :
    (runJvmRes fuel prog st).map f = some y :=
  Jvm.runJvmRes_map_of_runJvmResFast0 algHooks f fuel prog st y hpc hfast

theorem runJvmValFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepBlockChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmValFast_stepBlockChunk algHooks maxSteps fuel prog pc instrs st

theorem runJvmValFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st = evalBranchInstrCons f1 prog pc instr rest st :=
  Jvm.runJvmValFast_at_branch_cons algHooks f1 prog pc instr rest st hbr

theorem runJvmResFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResBlockChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmResFast_stepBlockChunk algHooks maxSteps fuel prog pc instrs st

theorem runJvmResFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st = evalResBranchInstrCons f1 prog pc instr rest st :=
  Jvm.runJvmResFast_at_branch_cons algHooks f1 prog pc instr rest st hbr

theorem runJvmValFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ rest', rest = .lconst 4294967295 :: .land :: rest')) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmValFast f1 prog (pc + 1) rest st'
        else runJvmValFast f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some v
      | .inr none => none := by
  dsimp only [runJvmValFast, stepInstr]
  rw [Jvm.runJvmValFast_step_nonbranch algHooks f1 prog pc instr rest st hbr hno]
  cases Jvm.stepInstr algHooks instr { st with pc := pc } with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

theorem runJvmResFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmResFast f1 prog (pc + 1) rest st'
        else runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some (v, { st with pc := pc })
      | .inr none => none := by
  dsimp only [runJvmResFast, stepInstr]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks f1 prog pc instr rest st hbr hno]
  cases Jvm.stepInstr algHooks instr { st with pc := pc } with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl

private partial def reduceAlgExtraProj (sub : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  let sub := sub.consumeMData
  let r := Jvm.Tactics.reduceJvmStateProj [``initJvmState] reduceAlgExtraProj
  if let .proj ``AlgHeap i h := sub then
    let h' ← r h
    if h'.isAppOfArity ``AlgHeap.mk 3 then
      return some (← r (h'.getArg! i))
    return some (.proj ``AlgHeap i h')
  if let some n := sub.getAppFn.constName? then
    if sub.getAppNumArgs == 1 &&
       (n == ``AlgHeap.arenas || n == ``AlgHeap.u64Arrays || n == ``AlgHeap.asciiArrays) then
      let i := if n == ``AlgHeap.arenas then 0
        else if n == ``AlgHeap.u64Arrays then 1
        else 2
      let h' ← r sub.appArg!
      if h'.isAppOfArity ``AlgHeap.mk 3 then
        return some (← r (h'.getArg! i))
      return some (Lean.mkApp sub.getAppFn h')
    if n == ``AlgHeap.mk && sub.getAppNumArgs == 3 then
      let args := sub.getAppArgs
      return some (Lean.mkApp3 sub.getAppFn (← r args[0]!) (← r args[1]!) (← r args[2]!))
  return none

abbrev whnfUnfoldInitJvmState := Jvm.Tactics.whnfUnfoldInitJvmState [``initJvmState]

def reduceStateProj : Lean.Expr → Lean.MetaM Lean.Expr :=
  Jvm.Tactics.reduceJvmStateProj [``initJvmState] reduceAlgExtraProj

private partial def normJvmNat (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if let some n := Jvm.Tactics.natLit? e then
    return Lean.mkNatLit n
  let e' ← reduceStateProj e
  let e' ← Lean.Meta.whnf e'
  if let some n := Jvm.Tactics.natLit? e' then
    return Lean.mkNatLit n
  if e'.isAppOfArity ``Nat.succ 1 then
    let a ← normJvmNat (e'.getArg! 0)
    if let some n := Jvm.Tactics.natLit? a then
      return Lean.mkNatLit (n + 1)
    return Lean.mkApp (Lean.mkConst ``Nat.succ) a
  if e'.isAppOfArity ``Nat.add 2 then
    let a ← normJvmNat (e'.getArg! 0)
    let b ← normJvmNat (e'.getArg! 1)
    if let (some na, some nb) := (Jvm.Tactics.natLit? a, Jvm.Tactics.natLit? b) then
      return Lean.mkNatLit (na + nb)
    return Lean.mkApp2 (Lean.mkConst ``Nat.add) a b
  return e'

private def normJvmStatePc (st : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if st.isAppOfArity ``Jvm.JvmState.mk 7 then
    let args := st.getAppArgs
    let pc' ← normJvmNat args[2]!
    return Lean.mkAppN st.getAppFn #[args[0]!, args[1]!, pc', args[3]!, args[4]!, args[5]!, args[6]!]
  return st

private partial def cleanJvmBlkPc (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if e.isAppOfArity ``Jvm.BlockChunkRes.cont 6 || e.isAppOfArity ``Jvm.BlockResChunkRes.cont 6 then
    let args := e.getAppArgs
    let st' ← normJvmStatePc args[5]!
    return Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, st']
  if e.isAppOfArity ``Jvm.BlockChunkRes.jump 4 || e.isAppOfArity ``Jvm.BlockResChunkRes.jump 4 then
    let args := e.getAppArgs
    let st' ← normJvmStatePc args[3]!
    return Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, st']
  if e.isAppOfArity ``Jvm.JvmState.mk 7 then
    return ← normJvmStatePc e
  if e.isAppOfArity ``Bool.rec 4 then
    let args := e.getAppArgs
    let args' ← args.mapM fun a => do
      if a.isLambda then
        Lean.Meta.lambdaTelescope a fun xs body => do
          Lean.Meta.mkLambdaFVars xs (← cleanJvmBlkPc body)
      else
        return a
    return Lean.mkAppN e.getAppFn args'
  return e

def normJvmExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e' ← Jvm.Tactics.normJvmBlkExpr [``initJvmState] reduceAlgExtraProj e
  cleanJvmBlkPc e'

elab "jvm_whnf_blk" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

abbrev evalNatLit? := Jvm.Tactics.evalNatLit?

abbrev foldInitLocals := Jvm.Tactics.foldInitLocals

def normJvmLocalsExpr : Lean.Expr → Lean.MetaM Lean.Expr :=
  Jvm.Tactics.normJvmLocalsExpr [``initJvmState] reduceAlgExtraProj
    [``AlgHeap.arenas, ``AlgHeap.u64Arrays, ``AlgHeap.asciiArrays]

elab "norm_jvm_locals" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmLocalsExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

@[simp] theorem algHooks_checkInstanceOf : algHooks.checkInstanceOf = checkInstanceOf := rfl

@[simp] theorem evalInstanceOf_algHooks_ext (jh : Jvm.JvmHeap AlgExt) (cls : String) (e : AlgExt) :
    Jvm.evalInstanceOf algHooks jh cls (.ext e) = checkInstanceOf cls (.ext e) := rfl

@[simp] theorem checkInstanceOf_level4_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.ext (.mc (.level4Node h nw ne sw se))) = true := rfl

@[simp] theorem checkInstanceOf_level4_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.ext (.mc (.cellNode h nw ne sw se))) = false := rfl

@[simp] theorem checkInstanceOf_cell_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.ext (.mc (.level4Node h nw ne sw se))) = false := rfl

@[simp] theorem checkInstanceOf_cell_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.ext (.mc (.cellNode h nw ne sw se))) = true := rfl

export Jvm (ui32_beq_0_0 ui32_beq_1_0 option_map_ite)

abbrev fastDropListEq := Jvm.Tactics.fastDropListEq

def normRunTail : Lean.Expr → Lean.MetaM (Lean.Expr × Option Lean.Expr) :=
  Jvm.Tactics.normRunTailWith ``runJvmValFast ``runJvmResFast normJvmExpr

elab "jvm_whnf_run_args" : conv => do
  let e ← Lean.Elab.Tactic.Conv.getLhs
  let eTop := if e.isAppOfArity ``Option.map 4 then e else e
  if eTop.isAppOfArity ``Option.map 4 ||
     eTop.isAppOfArity ``runJvmValFast 5 || eTop.isAppOfArity ``runJvmResFast 5 then
    let (e', eqOpt) ← normRunTail eTop
    match eqOpt with
    | some eqP => Lean.Elab.Tactic.Conv.updateLhs e' eqP
    | none => Lean.Elab.Tactic.Conv.changeLhs e'
  else if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    let (t', teqOpt) ← normRunTail args[3]!
    let (f', feqOpt) ← normRunTail args[4]!
    let newE := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
    if teqOpt.isNone && feqOpt.isNone then
      Lean.Elab.Tactic.Conv.changeLhs newE
    else
      let teq ← match teqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl t') (← Lean.Meta.mkEq args[3]! t')
      let feq ← match feqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl f') (← Lean.Meta.mkEq args[4]! f')
      let pf3 := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!]
      let c1 ← Lean.Meta.mkCongrArg pf3 teq
      let c2 ← Lean.Meta.mkCongr c1 feq
      Lean.Elab.Tactic.Conv.updateLhs newE c2

abbrev unwrapRunLhs := Jvm.Tactics.unwrapRunLhs

def isRunJvmAtNonBranch : Lean.Elab.Tactic.TacticM Bool :=
  Jvm.Tactics.isRunJvmAtPred ``runJvmValFast ``runJvmResFast ``isBranchInstr

def isRunJvmAtForwardGoto : Lean.Elab.Tactic.TacticM Bool :=
  Jvm.Tactics.isRunJvmAtForwardGoto ``runJvmValFast ``runJvmResFast

theorem afterBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterBlockChunk (.cont f pc is st) prog = runJvmValFast f prog pc is st := rfl

theorem afterBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterBlockChunk (.jump f ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩) prog =
      runJvmValFast f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

theorem afterBlockChunk_done (res : Option JvmVal) (prog : List JvmInstr) :
    afterBlockChunk (.done res) prog = res := rfl

theorem afterResBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterResBlockChunk (.cont f pc is st) prog = runJvmResFast f prog pc is st := rfl

theorem afterResBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterResBlockChunk (.jump f ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩) prog =
      runJvmResFast f prog pc (prog.drop pc) ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ := rfl

theorem afterResBlockChunk_done (res : Option (JvmVal × JvmState)) (prog : List JvmInstr) :
    afterResBlockChunk (.done res) prog = res := rfl

private theorem option_map_some' {α β : Type} (f : α → β) (x : α) :
    Option.map f (some x) = some (f x) := rfl

private theorem option_map_none' {α β : Type} (f : α → β) :
    Option.map f none = none := rfl

private theorem evalBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v == 0 then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifeq algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifeq_bool (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if !b then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifeq_bool algHooks f1 prog pc target rest pc0 b s locs jh hp

private theorem evalBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if !(v == 0) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifne algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifne_bool (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if b then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifne_bool algHooks f1 prog pc target rest pc0 b s locs jh hp

private theorem evalBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.slt 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_iflt algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.sle 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifle algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).slt v.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifgt algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).sle v.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifge algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifnull algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if !v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_ifnonnull algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a == b then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_if_icmpeq algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if !(a == b) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_if_icmpne algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.slt b.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalBranchInstrCons_if_icmplt algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast f1 prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := rfl

private theorem evalResBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v == 0 then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifeq algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifeq_bool (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if !b then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifeq_bool algHooks f1 prog pc target rest pc0 b s locs jh hp

private theorem evalResBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if !(v == 0) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifne algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifne_bool (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b : Bool) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, .bool b :: s, locs, jh, hp⟩ =
      if b then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifne_bool algHooks f1 prog pc target rest pc0 b s locs jh hp

private theorem evalResBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.slt 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_iflt algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if v.toBitVec.sle 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifle algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).slt v.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifgt algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, .i32 v :: s, locs, jh, hp⟩ =
      if (0#32).sle v.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifge algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifnull algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, jh, hp⟩ =
      if !v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_ifnonnull algHooks f1 prog pc target rest pc0 v s locs jh hp

private theorem evalResBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a == b then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_if_icmpeq algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalResBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if !(a == b) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_if_icmpne algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalResBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, hp⟩ =
      if a.toBitVec.slt b.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, hp⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, hp⟩ :=
  Jvm.evalResBranchInstrCons_if_icmplt algHooks f1 prog pc target rest pc0 b a s locs jh hp

private theorem evalResBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    evalResBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := rfl

def rwEvalBranchByInstr (isRes : Bool) (instr : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let some n := instr.consumeMData.getAppFn.constName? | return ()
  let thms : List Lean.Name :=
    if !isRes then
      if n == ``Jvm.JvmInstr.ifeq then [``evalBranchInstrCons_ifeq, ``evalBranchInstrCons_ifeq_bool]
      else if n == ``Jvm.JvmInstr.ifne then [``evalBranchInstrCons_ifne, ``evalBranchInstrCons_ifne_bool]
      else if n == ``Jvm.JvmInstr.iflt then [``evalBranchInstrCons_iflt]
      else if n == ``Jvm.JvmInstr.ifle then [``evalBranchInstrCons_ifle]
      else if n == ``Jvm.JvmInstr.ifgt then [``evalBranchInstrCons_ifgt]
      else if n == ``Jvm.JvmInstr.ifge then [``evalBranchInstrCons_ifge]
      else if n == ``Jvm.JvmInstr.ifnull then [``evalBranchInstrCons_ifnull]
      else if n == ``Jvm.JvmInstr.ifnonnull then [``evalBranchInstrCons_ifnonnull]
      else if n == ``Jvm.JvmInstr.if_icmpeq then [``evalBranchInstrCons_if_icmpeq]
      else if n == ``Jvm.JvmInstr.if_icmpne then [``evalBranchInstrCons_if_icmpne]
      else if n == ``Jvm.JvmInstr.if_icmplt then [``evalBranchInstrCons_if_icmplt]
      else if n == ``Jvm.JvmInstr.goto then [``evalBranchInstrCons_goto]
      else []
    else
      if n == ``Jvm.JvmInstr.ifeq then [``evalResBranchInstrCons_ifeq, ``evalResBranchInstrCons_ifeq_bool]
      else if n == ``Jvm.JvmInstr.ifne then [``evalResBranchInstrCons_ifne, ``evalResBranchInstrCons_ifne_bool]
      else if n == ``Jvm.JvmInstr.iflt then [``evalResBranchInstrCons_iflt]
      else if n == ``Jvm.JvmInstr.ifle then [``evalResBranchInstrCons_ifle]
      else if n == ``Jvm.JvmInstr.ifgt then [``evalResBranchInstrCons_ifgt]
      else if n == ``Jvm.JvmInstr.ifge then [``evalResBranchInstrCons_ifge]
      else if n == ``Jvm.JvmInstr.ifnull then [``evalResBranchInstrCons_ifnull]
      else if n == ``Jvm.JvmInstr.ifnonnull then [``evalResBranchInstrCons_ifnonnull]
      else if n == ``Jvm.JvmInstr.if_icmpeq then [``evalResBranchInstrCons_if_icmpeq]
      else if n == ``Jvm.JvmInstr.if_icmpne then [``evalResBranchInstrCons_if_icmpne]
      else if n == ``Jvm.JvmInstr.if_icmplt then [``evalResBranchInstrCons_if_icmplt]
      else if n == ``Jvm.JvmInstr.goto then [``evalResBranchInstrCons_goto]
      else []
  for tn in thms do
    let id := Lean.mkIdent tn
    let pre ← Lean.Elab.Tactic.getMainTarget
    Lean.Elab.Tactic.evalTactic (← `(tactic| try rw [$id:ident]))
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return ()
    let post ← Lean.Elab.Tactic.getMainTarget
    if post != pre then return ()

abbrev rwOptionMapResult := Jvm.Tactics.rwOptionMapResult

elab "jvm_step_one_chunk" : tactic => do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if isRes then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_stepBlockChunk 40]))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepBlockChunk 40]))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; arg 1; jvm_whnf_blk)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
    let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let (afterApp, _) := unwrapRunLhs lhs2
    let chunkRes := (afterApp.getArg! 0).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if !isRes then
        if cn == ``Jvm.BlockChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``Jvm.BlockChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``Jvm.BlockChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``Jvm.BlockResChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``Jvm.BlockResChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``Jvm.BlockResChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_done]))
          rwOptionMapResult
    if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))

private theorem ite_bool_eq_true_left {α : Type} {b : Bool} (h : b = true) (t e : α) :
    (if b = true then t else e) = t := Jvm.ite_bool_eq_true_left h t e

private theorem ite_bool_eq_true_right {α : Type} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e := Jvm.ite_bool_eq_true_right h t e

elab "reduce_top_mc_ite" : tactic => Lean.Elab.Tactic.withMainContext do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, rhs) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  let (hasMap, mapFn, mapArgs, iteExpr) :=
    if lhs.isAppOfArity ``Option.map 4 then
      (true, lhs.getAppFn, lhs.getAppArgs, lhs.appArg!.consumeMData)
    else
      (false, lhs, #[], lhs)
  if !iteExpr.isAppOfArity ``ite 5 then return ()
  let args := iteExpr.getAppArgs
  let cond := args[1]!.consumeMData
  if !cond.isAppOfArity ``Eq 3 then return ()
  let b := cond.getArg! 1
  let eqTrue ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.true)
  let eqFalse ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.false)
  let saved ← Lean.Elab.Tactic.getGoals
  let g ← Lean.Elab.Tactic.getMainGoal
  let tryClose (goalTy : Lean.Expr) (thmName : Lean.Name) (branchExpr : Lean.Expr) :
      Lean.Elab.Tactic.TacticM Bool := do
    let mvar ← Lean.Meta.mkFreshExprMVar goalTy
    Lean.Elab.Tactic.setGoals [mvar.mvarId!]
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp only [algHooks_checkInstanceOf, evalInstanceOf_algHooks_ext, checkInstanceOf_level4_level4, checkInstanceOf_level4_cell,
          checkInstanceOf_cell_level4, checkInstanceOf_cell_cell,
          ui32_beq_0_0, ui32_beq_1_0, eq_self_iff_true,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, beq_self_eq_true, ite_true, ite_false]))
    catch _ =>
      Lean.Elab.Tactic.setGoals saved
      return false
    let rem ← Lean.Elab.Tactic.getUnsolvedGoals
    if rem.isEmpty then
      let pf ← Lean.instantiateMVars mvar
      let stepEq := Lean.mkAppN (Lean.mkConst thmName) #[args[0]!, b, pf, args[3]!, args[4]!]
      let fullEq ←
        if hasMap then
          let fn := Lean.mkApp3 mapFn mapArgs[0]! mapArgs[1]! mapArgs[2]!
          Lean.Meta.mkCongrArg fn stepEq
        else
          pure stepEq
      let newLhs :=
        if hasMap then
          Lean.mkAppN mapFn #[mapArgs[0]!, mapArgs[1]!, mapArgs[2]!, branchExpr]
        else branchExpr
      let newTgt ← Lean.Meta.mkEq newLhs rhs
      let newMvar ← Lean.Meta.mkFreshExprMVar newTgt
      g.assign (← Lean.Meta.mkEqTrans fullEq newMvar)
      Lean.Elab.Tactic.setGoals (newMvar.mvarId! :: saved.tail!)
      return true
    Lean.Elab.Tactic.setGoals saved
    return false
  if ← tryClose eqTrue ``ite_bool_eq_true_left args[3]! then return ()
  let _ ← tryClose eqFalse ``ite_bool_eq_true_right args[4]!

elab "jvm_step_nonbranch_chunks" : tactic => do
  for _ in [:40] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    if ← isRunJvmAtNonBranch then
      Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_one_chunk))
    else if ← isRunJvmAtForwardGoto then
      let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | break
      let (inner, isMap) := unwrapRunLhs lhs
      let isRes := inner.isAppOfArity ``runJvmResFast 5
      if isRes then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        if isMap then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 2; arg 1; whnf)
            (conv => lhs; arg 2; arg 3; whnf)
            (conv => lhs; arg 2; arg 4; whnf)
            (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          let (evalApp, _) := unwrapRunLhs lhs2
          rwEvalBranchByInstr isRes (evalApp.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (
              (conv => lhs; try rw [option_map_ite])
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 1; whnf)
            (conv => lhs; arg 3; whnf)
            (conv => lhs; arg 4; whnf)
            (conv => lhs; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          rwEvalBranchByInstr isRes (lhs2.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "jvm_step_branch_tail" : tactic => do
  if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return ()
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  let isVal := inner.isAppOfArity ``runJvmValFast 5
  if !isRes && !isVal then return ()
  try
    if isRes then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
  catch _ =>
    return ()
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; arg 1; whnf)
        (conv => lhs; arg 2; arg 3; whnf)
        (conv => lhs; arg 2; arg 4; whnf)
        (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      let (evalApp, _) := unwrapRunLhs lhs2
      rwEvalBranchByInstr isRes (evalApp.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; norm_jvm_locals)
        (conv => lhs; try rw [option_map_ite])
        reduce_top_mc_ite)))
      rwOptionMapResult
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 1; whnf)
        (conv => lhs; arg 3; whnf)
        (conv => lhs; arg 4; whnf)
        (conv => lhs; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      rwEvalBranchByInstr isRes (lhs2.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; norm_jvm_locals)
        reduce_top_mc_ite
        (conv => lhs; jvm_whnf_run_args))))

elab "jvm_step_blk0" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))

elab "jvm_step_blk" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))


end Algorithm.JvmVerification

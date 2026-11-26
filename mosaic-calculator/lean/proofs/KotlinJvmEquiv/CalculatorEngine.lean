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

import Jvm.Proofs
import Jvm.Tactics
import KotlinJvmBytecode

namespace MosaicCalculator.KotlinJvmVerification

open MosaicCalculator.JvmVerification
open MosaicCalculator.KotlinJvmBytecode
open MosaicCalculator.Model

/-! ### Engine Program Lookup, Hooks, and Heap Invariants -/

/-- Bytecode lookup table for all `CalculatorEngineKt` methods. -/
def engineProgLookup (fnTag : String) : Option (List JvmInstr) :=
  match fnTag with
  | "CalculatorEngineKt.checkedAdd" => some CalculatorEngineKt_checkedAdd_prog
  | "CalculatorEngineKt.checkedSub" => some CalculatorEngineKt_checkedSub_prog
  | "CalculatorEngineKt.checkedMul" => some CalculatorEngineKt_checkedMul_prog
  | "CalculatorEngineKt.checkedDiv" => some CalculatorEngineKt_checkedDiv_prog
  | "CalculatorEngineKt.applyOp" => some CalculatorEngineKt_applyOp_prog
  | "CalculatorEngineKt.reduceCalculatorState" => some CalculatorEngineKt_reduceCalculatorState_prog
  | "CalculatorEngineKt.mapTerminalKey" => some CalculatorEngineKt_mapTerminalKey_prog
  | "CalculatorEngineKt.formatDisplayLine" => some CalculatorEngineKt_formatDisplayLine_prog
  | _ => none

/-- Default verification hooks wired with `engineProgLookup` at depth 4 and sub-fuel 400. -/
abbrev engineHooks : Jvm.JvmHooks CalcExt CalcHeap :=
  mkCalcHooks engineProgLookup 4 400

/-- Predicate asserting a `resolveProg` map extends `engineProgLookup`. -/
def ExtendsEngineProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ fnTag prog, engineProgLookup fnTag = some prog → resolveProg fnTag = some prog

theorem engineProgLookup_extends : ExtendsEngineProgs engineProgLookup :=
  fun _ _ h => h

/-- Predicate asserting no engine static fields in `CalculatorEngineKt` helpers are overridden. -/
def HasEngineStaticsClean (jh : Jvm.JvmHeap CalcExt) : Prop :=
  ∀ cls fld,
    cls ≠ "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" →
    cls ≠ "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt" →
    jh.getStatic? cls fld = none

/-- Predicate asserting `CalculatorEngineKt$WhenMappings` enum switch arrays are populated in `jh`. -/
structure HasCalcWhenMappings (jh : Jvm.JvmHeap CalcExt) : Prop where
  opSwitch : ∃ opAddr,
    jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
      "$EnumSwitchMapping$0" = some (.heapRef opAddr) ∧
    jh.get? opAddr = some (.intArray #[1, 2, 3, 4])
  errSwitch : ∃ errAddr,
    jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings"
      "$EnumSwitchMapping$1" = some (.heapRef errAddr) ∧
    jh.get? errAddr = some (.intArray #[1, 2])
  staticsClean : HasEngineStaticsClean jh

theorem calcInitJvmHeap_hasWhenMappings : HasCalcWhenMappings calcInitJvmHeap where
  opSwitch := ⟨0, rfl, rfl⟩
  errSwitch := ⟨1, rfl, rfl⟩
  staticsClean := by
    intro cls fld hne1 _
    simp only [calcInitJvmHeap, Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?, Jvm.JvmHeap.alloc,
      List.filter]
    have hne1' : ("com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" == cls) = false :=
      beq_false_of_ne (Ne.symm hne1)
    simp [hne1']

instance (resolveProg : String → Option (List JvmInstr)) (d fuel : Nat) :
    Jvm.HasDefaultIsZero (mkCalcHooks resolveProg d fuel) where
  isZero?_eq := by cases d <;> rfl

/-! ### Fast Symbolic Block Stepper & Hook Step Lemmas -/

/-- Stop predicate for `stepBlockChunkWith`: halts on invokes, heap/static, casts, returns, branches. -/
def isCalcStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .invokedynamic _ _ _ | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .checkcast _ | .instanceof _ | .iaload | .ldiv | .athrow
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

section StepTactics

open Lean Elab Tactic Meta

def calcOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkCalcHooks
    |>.insert ``engineProgLookup
    |>.insert ``CalculatorEngineKt_checkedAdd_prog
    |>.insert ``CalculatorEngineKt_checkedSub_prog
    |>.insert ``CalculatorEngineKt_checkedMul_prog
    |>.insert ``CalculatorEngineKt_checkedDiv_prog
    |>.insert ``CalculatorEngineKt_applyOp_prog
    |>.insert ``CalculatorEngineKt_reduceCalculatorState_prog
    |>.insert ``CalculatorEngineKt_mapTerminalKey_prog
    |>.insert ``CalculatorEngineKt_formatDisplayLine_prog
    |>.insert ``Model.checkedAddModel
    |>.insert ``Model.checkedSubModel
    |>.insert ``Model.checkedMulModel
    |>.insert ``Model.checkedDivModel
    |>.insert ``Model.applyOpModel
    |>.insert ``Model.reduceCalculatorStateModel
    |>.insert ``Model.mapTerminalKeyModel
    |>.insert ``Model.formatDisplayLineModel
    |>.insert ``Model.jvmI64Div
    |>.insert ``Model.int64Min
    |>.insert ``Model.int64ToString

def calcInitConsts : List Name :=
  [``initCalcJvmState, ``Jvm.initJvmState]

elab "calc_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque calcOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr calcInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "calc_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr calcInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "calc_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque calcOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr calcInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith calcOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque calcOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque calcOpaqueConsts (whnf ba[5]!)
        let st' ← normSt ba[7]!
        let mut instrs' := ba[6]!
        let mut instrsEq : Option Expr := none
        if instrs'.isAppOfArity ``List.drop 3 then
          let da := instrs'.getAppArgs
          if let some n ← Jvm.Tactics.evalNatLit? da[1]! then
            let (rhs, eqP) ← Jvm.Tactics.fastDropListEq da[2]! n
            instrs' := rhs
            instrsEq := some eqP
        while instrs'.isLet do
          instrs' := instrs'.letBody!.instantiate1 instrs'.letValue!
        let newB := mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', instrs', st']
        match instrsEq with
        | none => return (newB, none)
        | some eqP =>
          let lam := mkLambda `x .default (← inferType ba[6]!)
            (mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', Expr.bvar 0, st'])
          let fullEq ← mkCongrArg lam eqP
          let prefixB := mkAppN b.getAppFn #[ba[0]!, ba[1]!, ba[2]!, fuel', ba[4]!, pc', ba[6]!, st']
          let defEq ← mkExpectedTypeHint (← mkEqRefl b) (← mkEq b prefixB)
          return (newB, some (← mkEqTrans defEq fullEq))
      else
        return (b, none)
    if let some (_, lhs, rhs) := tgt.consumeMData.eq? then
      let (lhs', eqOpt) ← normRun lhs
      match eqOpt with
      | none => return [← g.replaceTargetDefEq (← mkEq lhs' rhs)]
      | some eqP =>
        let mvar ← mkFreshExprMVar (← mkEq lhs' rhs)
        g.assign (← mkEqTrans eqP mvar)
        return [mvar.mvarId!]
    return [g]

def isCalcNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isCalcStop) instr)
      return br.isConstOf ``Bool.false
  return false

def isCalcForwardGoto : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr ← whnf (instrs.getArg! 1)
      if instr.isAppOfArity ``Jvm.JvmInstr.goto 1 then
        if let (some pcVal, some tgtVal) :=
            (← Jvm.Tactics.evalNatLit? (lhs.getArg! 5), ← Jvm.Tactics.evalNatLit? (instr.getArg! 0)) then
          return pcVal < tgtVal
  return false

elab "calc_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isCalcStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; calc_whnf_blk)))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let chunkRes := (lhs2.consumeMData.getArg! 3).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if cn == ``Jvm.BlockResChunkRes.cont then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_cont]))
      else if cn == ``Jvm.BlockResChunkRes.jump then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_jump]))
      else if cn == ``Jvm.BlockResChunkRes.done then
        evalTactic (← `(tactic| rw [Jvm.afterResBlockChunk_done]))
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_run_args)))

elab "calc_step_blk" : tactic => do
  for _ in [:40] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isCalcNonStop then
      evalTactic (← `(tactic| calc_step_one_chunk))
    else if ← isCalcForwardGoto then
      evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_run_args)))
      evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; arg 2; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 5; whnf)
          (conv => lhs; arg 7; calc_whnf_blk))))
        let tgt2 := (← getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
        if !(← getUnsolvedGoals).isEmpty then
          evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_locals; calc_norm_run_args)))
    else
      break

private theorem ite_isNull_boxedLong {α : Type _} (x : UInt64)
    {inst : Decidable ((Jvm.JvmVal.boxedLong x : JvmVal).isNull = true)} (t e : α) :
    (@ite α ((Jvm.JvmVal.boxedLong x : JvmVal).isNull = true) inst t e) = e :=
  ite_eq_right (by dsimp only [Jvm.JvmVal.isNull]; intro h; cases h)

private theorem ite_isNull_ext {α : Type _} (x : CalcExt)
    {inst : Decidable ((Jvm.JvmVal.ext x : JvmVal).isNull = true)} (t e : α) :
    (@ite α ((Jvm.JvmVal.ext x : JvmVal).isNull = true) inst t e) = e :=
  ite_eq_right (by dsimp only [Jvm.JvmVal.isNull]; intro h; cases h)

private theorem ite_isNull_null {α : Type _}
    {inst : Decidable ((Jvm.JvmVal.null : JvmVal).isNull = true)} (t e : α) :
    (@ite α ((Jvm.JvmVal.null : JvmVal).isNull = true) inst t e) = t :=
  ite_eq_left rfl

private theorem ite_isNull_match_some {α : Type _} (x : Int64)
    {inst : Decidable ((match some x with
      | some x => Jvm.JvmVal.boxedLong x.toUInt64 | none => .null : JvmVal).isNull = true)}
    (t e : α) :
    (@ite α ((match some x with
      | some x => Jvm.JvmVal.boxedLong x.toUInt64 | none => .null : JvmVal).isNull = true) inst t e) = e :=
  by dsimp only; exact ite_eq_right (by dsimp only [Jvm.JvmVal.isNull]; intro h; cases h)

private def evalResTag : CheckedEvalResult → UInt32
  | .error _ => 1
  | .value _ => 0

private theorem ite_match_err {α : Type _} {e : CalculatorError}
    {inst : Decidable ((evalResTag (.error e) == 0) = true)}
    (t e2 : α) :
    (@ite α ((evalResTag (.error e) == 0) = true) inst t e2) = e2 := by
  have h1 : (evalResTag (.error e) == 0) = false := rfl
  exact ite_eq_right (h := inst) (by rw [h1]; exact Bool.false_ne_true)

private theorem ite_match_val {α : Type _} {v : Int64}
    {inst : Decidable ((evalResTag (.value v) == 0) = true)}
    (t e2 : α) :
    (@ite α ((evalResTag (.value v) == 0) = true) inst t e2) = t := by
  have h0 : (evalResTag (.value v) == 0) = true := rfl
  exact ite_eq_left (h := inst) h0

private theorem u32_and_ite_t {α : Type _} {m b : UInt32} (h : (m &&& b != 0) = true) (t e : α) :
    (if (m &&& b != 0) = true then t else e) = t := ite_eq_left h

private theorem u32_and_ite_f {α : Type _} {m b : UInt32} (h : (m &&& b != 0) = false) (t e : α) :
    (if (m &&& b != 0) = true then t else e) = e :=
  ite_eq_right (by rw [h]; decide)

elab "calc_branch" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (
      (conv => lhs; arg 2; whnf)
      (conv => lhs; arg 4; whnf)
      (conv => lhs; arg 5; whnf)
      (conv => lhs; arg 7; calc_whnf_blk))))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| try (first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | rw [ite_isNull_boxedLong]
        | rw [ite_isNull_ext]
        | rw [ite_isNull_null]
        | rw [ite_isNull_match_some])))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; tactic => calc_norm_locals; calc_norm_run_args)))

end StepTactics

/-! ### Domain Hook & Instruction Step Lemmas -/

private theorem runJvmResFast_newClass_calc {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls : String} (hnsb : (cls == "java/lang/StringBuilder") = false)
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc (.newClass cls :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel) (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, mkCalcHooks] <;> rw [Jvm.ite_bool_eq_true_right hnsb]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg d subFuel) rfl (by simp) hs rfl

elab "unfold_calc_priv" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← g.getType
    let tgt' ← Lean.Meta.transform tgt fun e => do
      if let .const n _ := e.getAppFn then
        let s := n.toString
        if s.endsWith "checkCalcCast" || s.endsWith "resolveCalcStatic" ||
           s.endsWith "checkCalcInstanceOf" || s.endsWith "applyCalculatorStateCtor" ||
           s.endsWith "stepArrayLoad" || s.endsWith "isVoidStaticTarget" ||
           s.endsWith "assignParamLocalsAux" then
          if let some e' ← Lean.Meta.unfoldDefinition? e then
            return .visit e'
      return .continue
    return [← g.replaceTargetDefEq tgt']

@[irreducible] private def holdOpt (x : Option (JvmVal × JvmState)) :
    Option (JvmVal × JvmState) := x

private theorem runJvmRes_exists_fast0 {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fuel : Nat} {prog : List JvmInstr} {st0 : JvmState} {v : JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hpc : st0.pc = 0)
    (h : ∃ endSt, Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) fuel prog 0 prog st0 =
        some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    ∃ endSt, Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel prog st0 =
        some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp :=
  let ⟨endSt, h1, h2, h3⟩ := h
  ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ hpc h1, h2, h3⟩

private theorem exists_run_step {f g : Option (JvmVal × JvmState)}
    {v : JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (h1 : f = holdOpt g)
    (h2 : ∃ endSt, g = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    ∃ endSt, f = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  rw [holdOpt] at h1
  exact h1 ▸ h2

private theorem exists_run_done {f : Option (JvmVal × JvmState)}
    {v : JvmVal} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (h : f = some (v, ⟨pc, stk, locs, jh, hp⟩)) :
    ∃ endSt, f = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp :=
  ⟨⟨pc, stk, locs, jh, hp⟩, h, rfl, rfl⟩

private theorem exists_run_ite {c : Prop} [Decidable c] {t e : Option (JvmVal × JvmState)}
    {v : JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (ht : c → ∃ endSt, t = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp)
    (he : ¬ c → ∃ endSt, e = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    ∃ endSt, (if c then t else e) = some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  by_cases hc : c <;> simp [hc, ht, he]

private theorem runJvmResFast_getstatic_clean {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls fld desc : String} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hclean : jh.getStatic? cls fld = none)
    (hres : (mkCalcHooks resolveProg (d + 1) subFuel).resolveStatic ⟨pc, stk, locs, jh, hp⟩ cls fld desc = some v) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc (.getstatic cls fld desc :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.getstatic cls fld desc) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hclean, hres]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_getstatic_heap {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls fld desc : String} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hget : jh.getStatic? cls fld = some v) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc (.getstatic cls fld desc :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel) (.getstatic cls fld desc) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hget]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_areturn_calc {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc (.areturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkCalcHooks resolveProg d subFuel) f prog pc .areturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel) .areturn ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inr (some v) := by
    dsimp only [Jvm.stepInstr]
  rw [hs]

private theorem stepSpecial_evalError {resolveProg : String → Option (List JvmInstr)}
    {d subFuel pc : Nat} {e : CalculatorError} {cls : String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.stepInvokeSpecialGeneric (mkCalcHooks resolveProg (d + 1) subFuel)
        ⟨pc, .ext (.calcErr e) :: .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult$Error" "<init>"
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorError;)V" =
      .inl (some ⟨pc + 1, .ext (.evalRes (.error e)) :: stkRest, locs, jh, hp⟩) := rfl

private theorem stepSpecial_evalValue {resolveProg : String → Option (List JvmInstr)}
    {d subFuel pc : Nat} {v : UInt64} {cls : String} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.stepInvokeSpecialGeneric (mkCalcHooks resolveProg (d + 1) subFuel)
        ⟨pc, .i64 v :: .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult$Value" "<init>" "(J)V" =
      .inl (some ⟨pc + 1, .ext (.evalRes (.value v.toInt64)) :: stkRest, locs, jh, hp⟩) := rfl

private theorem stepInstr_checkcast_evalRes {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {r : CheckedEvalResult}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult" :: rest)
        ⟨pc0, .ext (.evalRes r) :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.evalRes r) :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult")
      ⟨pc, .ext (.evalRes r) :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.evalRes r) :: stkRest, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

private theorem jvmI64Div_toUInt64 (a b : Int64) (hb : b ≠ 0) :
    Jvm.jvmI64Div a.toUInt64 b.toUInt64 = some (Model.jvmI64Div a b).toUInt64 := by
  have hbu : (b.toUInt64 == 0) = false := by
    apply beq_false_of_ne
    intro h
    apply hb
    exact Int64.toBitVec_inj.mp (by simpa using congrArg UInt64.toBitVec h)
  simp only [Jvm.jvmI64Div, hbu, Bool.false_eq_true, ↓reduceIte, Model.jvmI64Div]
  congr 1
  apply UInt64.toBitVec_inj.mp
  change BitVec.sdiv a.toBitVec b.toBitVec =
    BitVec.ofInt 64 (BitVec.sdiv a.toBitVec b.toBitVec).toInt
  exact (BitVec.ofInt_toInt).symm

private theorem int64_toUInt64_toInt64 (a : Int64) : a.toUInt64.toInt64 = a := by
  cases a; rfl

private theorem int64_beq_iff_toUInt64 (a b : Int64) :
    (a == b) = (a.toUInt64 == b.toUInt64) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : a.toUInt64 ≠ b.toUInt64 :=
      fun heq => h (Int64.toBitVec_inj.mp (by simpa using congrArg UInt64.toBitVec heq))
    rw [beq_false_of_ne h, beq_false_of_ne hne]

private theorem runJvmResFast_ldiv {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {va vb : UInt64} (hb : vb ≠ 0)
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc (.ldiv :: rest)
        ⟨pc0, .i64 vb :: .i64 va :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (Model.jvmI64Div va.toInt64 vb.toInt64).toUInt64 :: stkRest, locs, jh, hp⟩ := by
  have hdiv : Jvm.jvmI64Div va vb = some (Model.jvmI64Div va.toInt64 vb.toInt64).toUInt64 := by
    have hnb : vb.toInt64 ≠ 0 :=
      fun h => hb (UInt64.toBitVec_inj.mp (by simpa using congrArg Int64.toBitVec h))
    have heq := jvmI64Div_toUInt64 va.toInt64 vb.toInt64 hnb
    simpa using heq
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel) .ldiv
      ⟨pc, .i64 vb :: .i64 va :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .i64 (Model.jvmI64Div va.toInt64 vb.toInt64).toUInt64 :: stkRest, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.JvmVal.asI64?] <;> rw [hdiv]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem lcmp_ifge_iff_nslt (x : UInt64) :
    ((0#32).sle (if (x == 0) = true then (0 : UInt32)
      else if x.toBitVec.slt (UInt64.toBitVec 0) = true then 4294967295 else 1).toBitVec = true) ↔
    x.toBitVec.slt 0#64 = false := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hnx : (x == 0) = false := beq_false_of_ne hx
    cases hs : x.toBitVec.slt 0#64
    · have hs' : x.toBitVec.slt (UInt64.toBitVec 0) = false := hs
      simp only [hnx, hs', Bool.false_eq_true, ↓reduceIte]
      decide
    · have hs' : x.toBitVec.slt (UInt64.toBitVec 0) = true := hs
      simp only [hnx, hs', ↓reduceIte]
      decide

private theorem lcmp_ifeq_iff_eq (x y : UInt64) :
    ((if (x == y) = true then (0 : UInt32)
      else if x.toBitVec.slt y.toBitVec = true then 4294967295 else 1) == 0) = true ↔
    x = y := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : (x == y) = false := beq_false_of_ne hxy
    by_cases hs : x.toBitVec.slt y.toBitVec = true <;>
      simp only [hne, hs, Bool.false_eq_true, ↓reduceIte] <;>
      exact ⟨fun h => absurd h (by decide), fun h => absurd h hxy⟩

private theorem lcmp_ifne_iff_ne (x y : UInt64) :
    (!(if (x == y) = true then (0 : UInt32)
      else if x.toBitVec.slt y.toBitVec = true then 4294967295 else 1) == 0) = true ↔
    x ≠ y := by
  have h := lcmp_ifeq_iff_eq x y
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h ⊢
  exact not_congr h

/-! ### 1. `checkedAdd`, `checkedSub`, `checkedMul`, `checkedDiv` -/

theorem checkedAdd_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (a b : Int64) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hc : HasEngineStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_checkedAdd_prog
        (initCalcJvmState [(0, .i64 a.toUInt64), (2, .i64 b.toUInt64)] hp jh) =
        some (.ext (.evalRes (checkedAddModel a b)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedAdd_prog]
    calc_step_blk
    calc_branch
    unfold holdOpt
    rfl
  · apply exists_run_ite
    · intro hge
      rw [lcmp_ifge_iff_nslt] at hge
      simp only [checkedAddModel, hge, Bool.false_eq_true, ↓reduceIte]
      apply exists_run_done
      calc_norm_run_args
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
      rw [stepInstr_checkcast_evalRes]
      rw [runJvmResFast_areturn_calc]
    · intro hge
      rw [lcmp_ifge_iff_nslt] at hge
      have hslt : (((a.toUInt64 ^^^ (a.toUInt64 + b.toUInt64)) &&&
          (b.toUInt64 ^^^ (a.toUInt64 + b.toUInt64))).toBitVec.slt 0#64) = true := by
        cases hs : ((a.toUInt64 ^^^ (a.toUInt64 + b.toUInt64)) &&&
            (b.toUInt64 ^^^ (a.toUInt64 + b.toUInt64))).toBitVec.slt 0#64
        · exact absurd hs hge
        · rfl
      simp only [checkedAddModel, hslt, ↓reduceIte]
      apply exists_run_done
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
      rw [stepInstr_checkcast_evalRes]
      calc_step_blk
      calc_norm_run_args
      rw [runJvmResFast_areturn_calc]

theorem checkedSub_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (a b : Int64) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hc : HasEngineStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_checkedSub_prog
        (initCalcJvmState [(0, .i64 a.toUInt64), (2, .i64 b.toUInt64)] hp jh) =
        some (.ext (.evalRes (checkedSubModel a b)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedSub_prog]
    calc_step_blk
    calc_branch
    unfold holdOpt
    rfl
  · apply exists_run_ite
    · intro hge
      rw [lcmp_ifge_iff_nslt] at hge
      simp only [checkedSubModel, hge, Bool.false_eq_true, ↓reduceIte]
      apply exists_run_done
      calc_norm_run_args
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
      rw [stepInstr_checkcast_evalRes]
      rw [runJvmResFast_areturn_calc]
    · intro hge
      rw [lcmp_ifge_iff_nslt] at hge
      have hslt : (((a.toUInt64 ^^^ b.toUInt64) &&&
          (a.toUInt64 ^^^ (a.toUInt64 - b.toUInt64))).toBitVec.slt 0#64) = true := by
        cases hs : ((a.toUInt64 ^^^ b.toUInt64) &&&
            (a.toUInt64 ^^^ (a.toUInt64 - b.toUInt64))).toBitVec.slt 0#64
        · exact absurd hs hge
        · rfl
      simp only [checkedSubModel, hslt, ↓reduceIte]
      apply exists_run_done
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
      rw [stepInstr_checkcast_evalRes]
      calc_step_blk
      calc_norm_run_args
      rw [runJvmResFast_areturn_calc]

private theorem int64_toUInt64_inj {a b : Int64} (h : a.toUInt64 = b.toUInt64) : a = b :=
  Int64.toBitVec_inj.mp (by simpa using congrArg UInt64.toBitVec h)

private theorem checkedMul_tail_equiv (resolveProg : String → Option (List JvmInstr))
    (d1 subFuel f : Nat) (hf : 22 ≤ f) (a b : Int64) (hb : b ≠ 0) (hp : CalcHeap)
    (jh : Jvm.JvmHeap CalcExt) (hc : HasEngineStaticsClean jh) :
    let res : Int64 := (a.toUInt64 * b.toUInt64).toInt64
    let expected := if Model.jvmI64Div res b != a then CheckedEvalResult.error .overflow else .value res
    ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d1 + 1) subFuel) f CalculatorEngineKt_checkedMul_prog 36
        (List.drop 36 CalculatorEngineKt_checkedMul_prog)
        ⟨36, [],
          setLocal (setLocal (fun _ => .i32 0) 0 (.i64 a.toUInt64)) 2 (.i64 b.toUInt64), jh, hp⟩ =
        some (.ext (.evalRes expected), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  intro res expected
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedMul_prog, List.drop]
    calc_step_blk
    have hbu : b.toUInt64 ≠ 0 := fun h => hb (int64_toUInt64_inj h)
    rw [runJvmResFast_ldiv hbu]
    calc_step_blk
    calc_branch
    unfold holdOpt
    rfl
  · apply exists_run_ite
    · intro heq
      rw [lcmp_ifeq_iff_eq] at heq
      have hdiv : Model.jvmI64Div res b = a := by
        have := int64_toUInt64_inj heq
        simpa [res, int64_toUInt64_toInt64] using this
      have hne_b : (Model.jvmI64Div res b != a) = false := by simp [hdiv]
      simp only [expected, hne_b, Bool.false_eq_true, ↓reduceIte]
      apply exists_run_done
      calc_norm_run_args
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
      rw [stepInstr_checkcast_evalRes]
      rw [runJvmResFast_areturn_calc]
    · intro hne
      rw [lcmp_ifeq_iff_eq] at hne
      have hdiv : Model.jvmI64Div res b ≠ a := by
        intro h
        apply hne
        have h' : Model.jvmI64Div (a.toUInt64 * b.toUInt64).toInt64 b.toUInt64.toInt64 = a := by
          rw [int64_toUInt64_toInt64]
          exact h
        exact congrArg Int64.toUInt64 h'
      have hne_b : (Model.jvmI64Div res b != a) = true := bne_iff_ne.mpr hdiv
      simp only [expected, hne_b, ↓reduceIte]
      apply exists_run_done
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
      rw [stepInstr_checkcast_evalRes]
      calc_step_blk
      calc_norm_run_args
      rw [runJvmResFast_areturn_calc]

private theorem checkedMul_zero_branch (resolveProg : String → Option (List JvmInstr))
    (d1 subFuel f : Nat) (hf : 10 ≤ f) (a b : Int64) (hp : CalcHeap)
    (jh : Jvm.JvmHeap CalcExt) :
    ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d1 + 1) subFuel) f CalculatorEngineKt_checkedMul_prog 8
        (List.drop 8 CalculatorEngineKt_checkedMul_prog)
        ⟨8, [],
          setLocal (setLocal (fun _ => .i32 0) 0 (.i64 a.toUInt64)) 2 (.i64 b.toUInt64), jh, hp⟩ =
        some (.ext (.evalRes (.value 0)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply exists_run_done
  conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedMul_prog, List.drop]
  rw [runJvmResFast_newClass_calc (by decide)]
  calc_step_blk
  rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
  rw [stepInstr_checkcast_evalRes]
  rw [runJvmResFast_areturn_calc]
  rfl

private theorem checkedMul_overflow_branch (resolveProg : String → Option (List JvmInstr))
    (d1 subFuel f pc : Nat) (instrs : List JvmInstr) (locs : Nat → JvmVal)
    (hf : 10 ≤ f) (hpc : pc = 30) (hin : instrs = List.drop 30 CalculatorEngineKt_checkedMul_prog)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) (hc : HasEngineStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d1 + 1) subFuel) f CalculatorEngineKt_checkedMul_prog pc
        instrs ⟨pc, [], locs, jh, hp⟩ =
        some (.ext (.evalRes (.error .overflow)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  subst hpc; subst hin
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply exists_run_done
  conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedMul_prog, List.drop]
  rw [runJvmResFast_newClass_calc (by decide)]
  calc_step_blk
  rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
  rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
  rw [stepInstr_checkcast_evalRes]
  rw [runJvmResFast_areturn_calc]

theorem checkedMul_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 60 ≤ fuel)
    (a b : Int64) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hc : HasEngineStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_checkedMul_prog
        (initCalcJvmState [(0, .i64 a.toUInt64), (2, .i64 b.toUInt64)] hp jh) =
        some (.ext (.evalRes (checkedMulModel a b)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedMul_prog]
    calc_step_blk
    calc_branch
    unfold holdOpt
    rfl
  · apply exists_run_ite
    · intro ha0
      rw [lcmp_ifeq_iff_eq] at ha0
      have ha : a = 0 := int64_toUInt64_inj ha0
      simp only [checkedMulModel, ha, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      calc_norm_run_args
      apply checkedMul_zero_branch resolveProg d1 subFuel _ _ 0 b hp jh
      simp only [Nat.add_eq]; omega
    · intro ha0
      rw [lcmp_ifeq_iff_eq] at ha0
      have ha : a ≠ 0 := fun h => ha0 (congrArg Int64.toUInt64 h)
      apply exists_run_step
      · calc_step_blk
        calc_branch
        unfold holdOpt
        rfl
      · apply exists_run_ite
        · intro hb0
          rw [lcmp_ifne_iff_ne] at hb0
          have hb : b ≠ 0 := fun h => hb0 (congrArg Int64.toUInt64 h)
          have hnz : (a == 0 || b == 0) = false := by
            simp [beq_false_of_ne ha, beq_false_of_ne hb]
          simp only [checkedMulModel, hnz, Bool.false_eq_true, ↓reduceIte]
          apply exists_run_step
          · calc_step_blk
            calc_branch
            unfold holdOpt
            rfl
          · apply exists_run_ite
            · intro hna_min
              rw [lcmp_ifne_iff_ne] at hna_min
              have ha_min : a ≠ int64Min := fun h => hna_min (congrArg Int64.toUInt64 h)
              apply exists_run_step
              · calc_step_blk
                calc_branch
                unfold holdOpt
                rfl
              · apply exists_run_ite
                · intro hnb_min
                  rw [lcmp_ifne_iff_ne] at hnb_min
                  have hb_min : b ≠ int64Min := fun h => hnb_min (congrArg Int64.toUInt64 h)
                  have hno :
                      ((a == int64Min && b == -1) || (b == int64Min && a == -1)) = false := by
                    simp [beq_false_of_ne ha_min, beq_false_of_ne hb_min]
                  simp only [hno, Bool.false_eq_true, ↓reduceIte]
                  apply checkedMul_tail_equiv resolveProg d1 subFuel _ _ a b hb hp jh hc
                  simp only [Nat.add_eq]; omega
                · intro hb_min'
                  rw [lcmp_ifne_iff_ne, Decidable.not_not] at hb_min'
                  have hb_min : b = int64Min := int64_toUInt64_inj hb_min'
                  apply exists_run_step
                  · calc_step_blk
                    calc_branch
                    unfold holdOpt
                    rfl
                  · apply exists_run_ite
                    · intro hna_m1
                      rw [lcmp_ifne_iff_ne] at hna_m1
                      have ha_m1 : a ≠ -1 := fun h => hna_m1 (congrArg Int64.toUInt64 h)
                      have hno :
                          ((a == int64Min && b == -1) || (b == int64Min && a == -1)) = false := by
                        simp [beq_false_of_ne ha_min, beq_false_of_ne ha_m1]
                      simp only [hno, Bool.false_eq_true, ↓reduceIte]
                      apply checkedMul_tail_equiv resolveProg d1 subFuel _ _ a b hb hp jh hc
                      simp only [Nat.add_eq]; omega
                    · intro ha_m1'
                      rw [lcmp_ifne_iff_ne, Decidable.not_not] at ha_m1'
                      have ha_m1 : a = -1 := int64_toUInt64_inj ha_m1'
                      simp only [hb_min, ha_m1, beq_self_eq_true, Bool.and_self,
                        Bool.or_true, ↓reduceIte]
                      apply checkedMul_overflow_branch resolveProg d1 subFuel _ _ _ _
                        (by simp only [Nat.add_eq]; omega) rfl rfl hp jh hc
            · intro ha_min'
              rw [lcmp_ifne_iff_ne, Decidable.not_not] at ha_min'
              have ha_min : a = int64Min := int64_toUInt64_inj ha_min'
              apply exists_run_step
              · calc_step_blk
                calc_branch
                unfold holdOpt
                rfl
              · apply exists_run_ite
                · intro hb_m1'
                  rw [lcmp_ifeq_iff_eq] at hb_m1'
                  have hb_m1 : b = -1 := int64_toUInt64_inj hb_m1'
                  simp only [ha_min, hb_m1, beq_self_eq_true, Bool.and_self,
                    Bool.true_or, ↓reduceIte]
                  apply checkedMul_overflow_branch resolveProg d1 subFuel _ _ _ _
                    (by simp only [Nat.add_eq]; omega) rfl rfl hp jh hc
                · intro hnb_m1
                  rw [lcmp_ifeq_iff_eq] at hnb_m1
                  have hb_m1 : b ≠ -1 := fun h => hnb_m1 (congrArg Int64.toUInt64 h)
                  apply exists_run_step
                  · calc_step_blk
                    calc_branch
                    unfold holdOpt
                    rfl
                  · apply exists_run_ite
                    · intro hnb_min
                      rw [lcmp_ifne_iff_ne] at hnb_min
                      have hb_min : b ≠ int64Min := fun h => hnb_min (congrArg Int64.toUInt64 h)
                      have hno :
                          ((a == int64Min && b == -1) || (b == int64Min && a == -1)) = false := by
                        simp [beq_false_of_ne hb_m1, beq_false_of_ne hb_min]
                      simp only [hno, Bool.false_eq_true, ↓reduceIte]
                      apply checkedMul_tail_equiv resolveProg d1 subFuel _ _ a b hb hp jh hc
                      simp only [Nat.add_eq]; omega
                    · intro hb_min'
                      rw [lcmp_ifne_iff_ne, Decidable.not_not] at hb_min'
                      have hb_min : b = int64Min := int64_toUInt64_inj hb_min'
                      apply exists_run_step
                      · calc_step_blk
                        calc_branch
                        unfold holdOpt
                        rfl
                      · apply exists_run_ite
                        · intro hna_m1
                          rw [lcmp_ifne_iff_ne] at hna_m1
                          have ha_m1 : a ≠ -1 := fun h => hna_m1 (congrArg Int64.toUInt64 h)
                          have hno : ((a == int64Min && b == -1) ||
                              (b == int64Min && a == -1)) = false := by
                            simp [beq_false_of_ne hb_m1, beq_false_of_ne ha_m1]
                          simp only [hno, Bool.false_eq_true, ↓reduceIte]
                          apply checkedMul_tail_equiv resolveProg d1 subFuel _ _ a b hb hp jh hc
                          simp only [Nat.add_eq]; omega
                        · intro ha_m1'
                          rw [lcmp_ifne_iff_ne, Decidable.not_not] at ha_m1'
                          have ha_m1 : a = -1 := int64_toUInt64_inj ha_m1'
                          simp only [hb_min, ha_m1, beq_self_eq_true, Bool.and_self,
                            Bool.or_true, ↓reduceIte]
                          apply checkedMul_overflow_branch resolveProg d1 subFuel _ _ _ _
                            (by simp only [Nat.add_eq]; omega) rfl rfl hp jh hc
        · intro hb0
          rw [lcmp_ifne_iff_ne, Decidable.not_not] at hb0
          have hb : b = 0 := int64_toUInt64_inj hb0
          simp only [checkedMulModel, hb, beq_self_eq_true, Bool.or_true, ↓reduceIte]
          apply checkedMul_zero_branch resolveProg d1 subFuel _ _ a 0 hp jh
          simp only [Nat.add_eq]; omega

theorem checkedDiv_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 35 ≤ fuel)
    (a b : Int64) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hc : HasEngineStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_checkedDiv_prog
        (initCalcJvmState [(0, .i64 a.toUInt64), (2, .i64 b.toUInt64)] hp jh) =
        some (.ext (.evalRes (checkedDivModel a b)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_checkedDiv_prog]
    calc_step_blk
    calc_branch
    unfold holdOpt
    rfl
  · apply exists_run_ite
    · intro hb0
      rw [lcmp_ifne_iff_ne] at hb0
      have hb : b ≠ 0 := fun h => hb0 (congrArg Int64.toUInt64 h)
      have hbz : (b == 0) = false := beq_false_of_ne hb
      simp only [checkedDivModel, hbz, Bool.false_eq_true, ↓reduceIte]
      apply exists_run_step
      · calc_step_blk
        calc_branch
        unfold holdOpt
        rfl
      · apply exists_run_ite
        · intro hna_min
          rw [lcmp_ifne_iff_ne] at hna_min
          have ha_min : a ≠ int64Min := fun h => hna_min (congrArg Int64.toUInt64 h)
          have hno : (a == int64Min && b == -1) = false := by simp [beq_false_of_ne ha_min]
          simp only [hno, Bool.false_eq_true, ↓reduceIte]
          apply exists_run_done
          calc_norm_run_args
          rw [runJvmResFast_newClass_calc (by decide)]
          calc_step_blk
          have hbu : b.toUInt64 ≠ 0 := fun h => hb (int64_toUInt64_inj h)
          rw [runJvmResFast_ldiv hbu]
          rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
          simp only [int64_toUInt64_toInt64]
          rw [stepInstr_checkcast_evalRes]
          rw [runJvmResFast_areturn_calc]
        · intro ha_min'
          rw [lcmp_ifne_iff_ne, Decidable.not_not] at ha_min'
          have ha_min : a = int64Min := int64_toUInt64_inj ha_min'
          apply exists_run_step
          · calc_step_blk
            calc_branch
            unfold holdOpt
            rfl
          · apply exists_run_ite
            · intro hnb_m1
              rw [lcmp_ifne_iff_ne] at hnb_m1
              have hb_m1 : b ≠ -1 := fun h => hnb_m1 (congrArg Int64.toUInt64 h)
              have hno : (a == int64Min && b == -1) = false := by simp [beq_false_of_ne hb_m1]
              simp only [hno, Bool.false_eq_true, ↓reduceIte]
              apply exists_run_done
              calc_norm_run_args
              rw [runJvmResFast_newClass_calc (by decide)]
              calc_step_blk
              have hbu : b.toUInt64 ≠ 0 := fun h => hb (int64_toUInt64_inj h)
              rw [runJvmResFast_ldiv hbu]
              rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalValue]
              simp only [int64_toUInt64_toInt64]
              rw [stepInstr_checkcast_evalRes]
              rw [runJvmResFast_areturn_calc]
            · intro hb_m1'
              rw [lcmp_ifne_iff_ne, Decidable.not_not] at hb_m1'
              have hb_m1 : b = -1 := int64_toUInt64_inj hb_m1'
              simp only [ha_min, hb_m1, beq_self_eq_true, Bool.and_self, ↓reduceIte]
              apply exists_run_done
              rw [runJvmResFast_newClass_calc (by decide)]
              calc_step_blk
              rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
              rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
              rw [stepInstr_checkcast_evalRes]
              calc_step_blk
              calc_norm_run_args
              rw [runJvmResFast_areturn_calc]
    · intro hb0
      rw [lcmp_ifne_iff_ne, Decidable.not_not] at hb0
      have hb : b = 0 := int64_toUInt64_inj hb0
      simp only [checkedDivModel, hb, beq_self_eq_true, ↓reduceIte]
      apply exists_run_done
      rw [runJvmResFast_newClass_calc (by decide)]
      calc_step_blk
      rw [runJvmResFast_getstatic_clean (hc _ _ (by decide) (by decide)) rfl]
      rw [Jvm.runJvmResFast_invokespecial_step _ stepSpecial_evalError]
      rw [stepInstr_checkcast_evalRes]
      calc_step_blk
      calc_norm_run_args
      rw [runJvmResFast_areturn_calc]

/-! ### 2. `applyOp` -/

private theorem runJvmResFast_checkNotNullParameter {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {msg : String} {obj : JvmVal}
    (hnn : obj.isNull = false) {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str msg :: obj :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str msg :: obj :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric] <;> simp [hnn]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_op_ordinal {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {op : CalculatorOp}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    let ord : UInt32 := match op with | .add => 0 | .sub => 1 | .mul => 2 | .div => 3
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" "ordinal"
          "()I" :: rest)
        ⟨pc0, .ext (.calcOp op) :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 ord :: stkRest, locs, jh, hp⟩ := by
  intro ord
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorOp" "ordinal" "()I")
      ⟨pc, .ext (.calcOp op) :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 ord :: stkRest, locs, jh, hp⟩) := by
    cases op <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_iaload {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {addr : Nat} {idx : UInt32} {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hnslt : idx.toBitVec.slt 0#32 = false) (hlt : idx.toNat < elems.size)
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) (f + 1) prog pc (.iaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 elems[idx.toNat] :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg d subFuel) .iaload
      ⟨pc, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 elems[idx.toNat] :: stkRest, locs, jh, hp⟩) := by
    cases d <;>
      dsimp only [Jvm.stepInstr] <;>
      unfold_calc_priv <;>
      dsimp only [Jvm.JvmVal.asI32?] <;>
      rw [hnslt] <;>
      simp [hget, hlt]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg d subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_invokestatic_checkedBin {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    (method : String) (subProg : List JvmInstr) (res : CheckedEvalResult)
    (hm : method = "checkedAdd" ∨ method = "checkedSub" ∨
      method = "checkedMul" ∨ method = "checkedDiv")
    (hres : resolveProg ("CalculatorEngineKt." ++ method) = some subProg)
    {a b : Int64} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (heq : ∃ endSt, Jvm.runJvmRes (mkCalcHooks resolveProg (d + 1) subFuel) subFuel subProg
        (initCalcJvmState [(0, .i64 a.toUInt64), (2, .i64 b.toUInt64)] hp jh) =
        some (.ext (.evalRes res), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 2) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt" method
          "(JJ)Lcom/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult;" :: rest)
        ⟨pc0, .i64 b.toUInt64 :: .i64 a.toUInt64 :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 2) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.evalRes res) :: stkRest, locs, jh, hp⟩ := by
  obtain ⟨endSt, hrun, hjh, hhp⟩ := heq
  have hstep : (mkCalcHooks resolveProg (d + 2) subFuel).stepInvokeStatic
      ⟨pc, .i64 b.toUInt64 :: .i64 a.toUInt64 :: stkRest, locs, jh, hp⟩
      "CalculatorEngineKt" method
      "(JJ)Lcom/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult;" =
      .inl (some ⟨pc + 1, .ext (.evalRes res) :: stkRest, locs, jh, hp⟩) := by
    rcases hm with rfl | rfl | rfl | rfl <;>
    ( (conv => lhs; whnf)
      rw [show normalizeCalcClass "CalculatorEngineKt" = "CalculatorEngineKt" from rfl]
      first
      | ( rw [show "CalculatorEngineKt" ++ "." ++ "checkedAdd" = "CalculatorEngineKt.checkedAdd"
            from by apply String.ext; simp]
          rw [show "CalculatorEngineKt." ++ "checkedAdd" = "CalculatorEngineKt.checkedAdd"
            from by apply String.ext; simp] at hres )
      | ( rw [show "CalculatorEngineKt" ++ "." ++ "checkedSub" = "CalculatorEngineKt.checkedSub"
            from by apply String.ext; simp]
          rw [show "CalculatorEngineKt." ++ "checkedSub" = "CalculatorEngineKt.checkedSub"
            from by apply String.ext; simp] at hres )
      | ( rw [show "CalculatorEngineKt" ++ "." ++ "checkedMul" = "CalculatorEngineKt.checkedMul"
            from by apply String.ext; simp]
          rw [show "CalculatorEngineKt." ++ "checkedMul" = "CalculatorEngineKt.checkedMul"
            from by apply String.ext; simp] at hres )
      | ( rw [show "CalculatorEngineKt" ++ "." ++ "checkedDiv" = "CalculatorEngineKt.checkedDiv"
            from by apply String.ext; simp]
          rw [show "CalculatorEngineKt." ++ "checkedDiv" = "CalculatorEngineKt.checkedDiv"
            from by apply String.ext; simp] at hres )
      rw [show Jvm.parseMethodParamTags
          "(JJ)Lcom/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult;" =
        ['J', 'J'] from by decide]
      dsimp only [List.length, List.take, List.drop, List.reverse, List.reverseAux]
      rw [hres]
      unfold_calc_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState] at hrun ⊢
      rw [hrun]
      dsimp only
      rw [hjh, hhp]
      rfl )
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 2) subFuel)
      (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt" method
        "(JJ)Lcom/alexvanyo/composelife/mosaiccalculator/CheckedEvalResult;")
      ⟨pc, .i64 b.toUInt64 :: .i64 a.toUInt64 :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.evalRes res) :: stkRest, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 2) subFuel) rfl (by simp) hs rfl

theorem applyOp_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsEngineProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsub : 60 ≤ subFuel) (hf : 25 ≤ fuel)
    (lhs : Int64) (op : CalculatorOp) (rhs : Int64) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_applyOp_prog
        (initCalcJvmState [(0, .i64 lhs.toUInt64), (2, .ext (.calcOp op)), (3, .i64 rhs.toUInt64)]
          hp jh) =
        some (.ext (.evalRes (applyOpModel lhs op rhs)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d2, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨opAddr, hopStatic, hopArr⟩ := hw.opSwitch
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_applyOp_prog]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    rw [runJvmResFast_getstatic_heap hopStatic]
    calc_step_blk
    rw [runJvmResFast_op_ordinal]
    rw [runJvmResFast_iaload hopArr (by cases op <;> decide) (by cases op <;> decide)]
    calc_branch
    dsimp only
    calc_norm_run_args
    unfold holdOpt
    rfl
  · cases op
    · apply exists_run_done
      calc_step_blk
      rw [runJvmResFast_invokestatic_checkedBin "checkedAdd" CalculatorEngineKt_checkedAdd_prog
        (checkedAddModel lhs rhs) (Or.inl rfl) (hext _ _ rfl)
        (checkedAdd_equiv resolveProg (d2 + 1) subFuel subFuel (by omega) (by omega)
          lhs rhs hp jh hw.staticsClean)]
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      rfl
    · apply exists_run_done
      calc_step_blk
      rw [runJvmResFast_invokestatic_checkedBin "checkedSub" CalculatorEngineKt_checkedSub_prog
        (checkedSubModel lhs rhs) (Or.inr (Or.inl rfl)) (hext _ _ rfl)
        (checkedSub_equiv resolveProg (d2 + 1) subFuel subFuel (by omega) (by omega)
          lhs rhs hp jh hw.staticsClean)]
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      rfl
    · apply exists_run_done
      calc_step_blk
      rw [runJvmResFast_invokestatic_checkedBin "checkedMul" CalculatorEngineKt_checkedMul_prog
        (checkedMulModel lhs rhs) (Or.inr (Or.inr (Or.inl rfl))) (hext _ _ rfl)
        (checkedMul_equiv resolveProg (d2 + 1) subFuel subFuel (by omega) hsub
          lhs rhs hp jh hw.staticsClean)]
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      rfl
    · apply exists_run_done
      calc_step_blk
      rw [runJvmResFast_invokestatic_checkedBin "checkedDiv" CalculatorEngineKt_checkedDiv_prog
        (checkedDivModel lhs rhs) (Or.inr (Or.inr (Or.inr rfl))) (hext _ _ rfl)
        (checkedDiv_equiv resolveProg (d2 + 1) subFuel subFuel (by omega) (by omega)
          lhs rhs hp jh hw.staticsClean)]
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      rfl

/-! ### 3. `reduceCalculatorState` -/

private theorem i2l_to_int32_int64 (d : UInt32) :
    UInt64.ofBitVec (d.toBitVec.signExtend 64) =
      ((Int32.ofInt d.toBitVec.toInt).toInt64).toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  change d.toBitVec.signExtend 64 = (Int32.ofInt d.toBitVec.toInt).toInt64.toBitVec
  have h1 : (Int32.ofInt d.toBitVec.toInt).toBitVec = d.toBitVec := by
    change BitVec.ofInt 32 d.toBitVec.toInt = d.toBitVec
    exact BitVec.ofInt_toInt
  change d.toBitVec.signExtend 64 = (Int32.ofInt d.toBitVec.toInt).toBitVec.signExtend 64
  rw [h1]

theorem runJvmResFast_instanceof_lit {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String} {v : JvmVal}
    (res : UInt32) {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hins : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) (.instanceof cls)
        ⟨pc, v :: stkRest, locs, jh, hp⟩ =
        .inl (some ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.instanceof cls :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hins rfl

theorem runJvmResFast_checkcast_calc {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String} {v : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hcc : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) (.checkcast cls)
        ⟨pc, v :: stkRest, locs, jh, hp⟩ =
        .inl (some ⟨pc + 1, v :: stkRest, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.checkcast cls :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stkRest, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hcc rfl

theorem runJvmResFast_invokevirtual_step {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls method desc : String}
    {stk0 stk1 : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hstep : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
        (.invokevirtual cls method desc) ⟨pc, stk0, locs, jh, hp⟩ =
        .inl (some ⟨pc + 1, stk1, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual cls method desc :: rest) ⟨pc0, stk0, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk1, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hstep rfl

private theorem runJvmResFast_areEqual_step {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal} {res : Bool}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hbeq : Jvm.JvmVal.beqVal beqCalcExt a b = res)
    (ha : a.equalsModeled jh = true := by rfl) (hb : b.equalsModeled jh = true := by rfl) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual"
          "(Ljava/lang/Object;Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, b :: a :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .bool res :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "areEqual"
        "(Ljava/lang/Object;Ljava/lang/Object;)Z")
      ⟨pc, b :: a :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .bool (Jvm.JvmVal.beqVal beqCalcExt a b) :: stkRest, locs, jh, hp⟩) :=
    Jvm.stepInstr_areEqual _ ha hb
  rw [hbeq] at hs
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runJvmResFast_longValueOf {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {x : UInt64}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "java/lang/Long" "valueOf" "(J)Ljava/lang/Long;" :: rest)
        ⟨pc0, .i64 x :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .boxedLong x :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.invokestatic "java/lang/Long" "valueOf" "(J)Ljava/lang/Long;")
      ⟨pc, .i64 x :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedLong x :: stkRest, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

theorem runJvmResFast_copyDefault {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {desc : String}
    {base out : CalculatorState} {dVal : UInt64} {mask : UInt32}
    {pOpndV pOpV entV errV marker : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hc : (mkCalcHooks resolveProg (d + 1) subFuel).stepInvokeStatic
        ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
          .ext (.calcState base) :: stkRest, locs, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "copy$default" desc =
        .inl (some ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "copy$default"
          desc :: rest)
        ⟨pc0, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
          .ext (.calcState base) :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "copy$default"
        desc)
      ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
        .ext (.calcState base) :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hc
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

set_option maxRecDepth 2048 in
theorem runJvmResFast_calcState_ctor {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls desc : String} {out : CalculatorState} {dVal : UInt64} {mask : UInt32}
    {pOpndV pOpV entV errV marker : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hc : (mkCalcHooks resolveProg (d + 1) subFuel).stepInvokeSpecial
        ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
          .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩
        "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "<init>" desc =
        .inl (some ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) (f + 1) prog pc
        (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "<init>"
          desc :: rest)
        ⟨pc0, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
          .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
      (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "<init>" desc)
      ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
        .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.calcState out) :: stkRest, locs, jh, hp⟩) := by
    have hgen : Jvm.stepInstr (mkCalcHooks resolveProg (d + 1) subFuel)
        (.invokespecial "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "<init>" desc)
        ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
          .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩ =
        (mkCalcHooks resolveProg (d + 1) subFuel).stepInvokeSpecial
          ⟨pc, marker :: .i32 mask :: errV :: entV :: pOpV :: pOpndV :: .i64 dVal ::
            .allocRef cls :: .allocRef cls :: stkRest, locs, jh, hp⟩
          "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "<init>" desc := rfl
    rw [hgen]
    exact hc
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 1) subFuel) rfl (by simp) hs rfl

macro "calc_iv" : tactic => `(tactic| focus (
  rw [runJvmResFast_invokevirtual_step]
  rotate_left 1
  rfl
  (conv => lhs; tactic => try calc_norm_run_args)))

macro "calc_io" : tactic => `(tactic| focus (
  first
  | ( rw [runJvmResFast_instanceof_lit 1]
      rotate_left 1
      dsimp only [Jvm.stepInstr, Jvm.evalInstanceOf, mkCalcHooks]
      unfold_calc_priv
      rfl )
  | ( rw [runJvmResFast_instanceof_lit 0]
      rotate_left 1
      dsimp only [Jvm.stepInstr, Jvm.evalInstanceOf, mkCalcHooks]
      unfold_calc_priv
      rfl )))

macro "calc_cc" : tactic => `(tactic| focus (
  rw [runJvmResFast_checkcast_calc]
  rotate_left 1
  dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, mkCalcHooks]
  unfold_calc_priv
  rfl))

macro "calc_cd" : tactic => `(tactic| focus (
  rw [runJvmResFast_copyDefault]
  rotate_left 1
  rfl))

macro "calc_cs" : tactic => `(tactic| focus (
  rw [runJvmResFast_calcState_ctor]
  rotate_left 1
  rfl))

set_option maxRecDepth 2048 in
private theorem runJvmResFast_invokestatic_applyOp {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {desc : String}
    (htags : Jvm.parseMethodParamTags desc = ['J', 'L', 'J'])
    (hres : resolveProg "CalculatorEngineKt.applyOp" = some CalculatorEngineKt_applyOp_prog)
    {lhs rhs : Int64} {op : CalculatorOp} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (heq : ∃ endSt, Jvm.runJvmRes (mkCalcHooks resolveProg (d + 2) subFuel) subFuel CalculatorEngineKt_applyOp_prog
        (initCalcJvmState [(0, .i64 lhs.toUInt64), (2, .ext (.calcOp op)), (3, .i64 rhs.toUInt64)]
          hp jh) =
        some (.ext (.evalRes (applyOpModel lhs op rhs)), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 3) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt" "applyOp" desc :: rest)
        ⟨pc0, .i64 rhs.toUInt64 :: .ext (.calcOp op) :: .i64 lhs.toUInt64 :: stkRest, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d + 3) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.evalRes (applyOpModel lhs op rhs)) :: stkRest, locs, jh, hp⟩ := by
  obtain ⟨endSt, hrun, hjh, hhp⟩ := heq
  have hstep : (mkCalcHooks resolveProg (d + 3) subFuel).stepInvokeStatic
      ⟨pc, .i64 rhs.toUInt64 :: .ext (.calcOp op) :: .i64 lhs.toUInt64 :: stkRest, locs, jh, hp⟩
      "CalculatorEngineKt" "applyOp" desc =
      .inl (some ⟨pc + 1, .ext (.evalRes (applyOpModel lhs op rhs)) :: stkRest, locs, jh, hp⟩) := by
    conv => lhs; whnf
    rw [show normalizeCalcClass "CalculatorEngineKt" = "CalculatorEngineKt" from rfl]
    rw [show "CalculatorEngineKt" ++ "." ++ "applyOp" = "CalculatorEngineKt.applyOp"
      from by apply String.ext; simp]
    simp only [htags]
    dsimp only [List.length]
    cases (stkRest.length + 1 + 1 + 1).decLt (Jvm.parseMethodParamTags desc).length with
    | isTrue h =>
      rw [htags] at h
      dsimp only [List.length] at h
      omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      rw [hres]
      unfold_calc_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState] at hrun ⊢
      rw [hrun]
      dsimp only
      rw [hjh, hhp]
      rfl
  have hs : Jvm.stepInstr (mkCalcHooks resolveProg (d + 3) subFuel)
      (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt" "applyOp" desc)
      ⟨pc, .i64 rhs.toUInt64 :: .ext (.calcOp op) :: .i64 lhs.toUInt64 :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.evalRes (applyOpModel lhs op rhs)) :: stkRest, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    exact hstep
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks resolveProg (d + 3) subFuel) rfl (by simp) hs rfl

private theorem reduceDigit_finish_equiv (resolveProg : String → Option (List JvmInstr))
    (d3 subFuel f pc : Nat) (instrs : List JvmInstr) (locs : Nat → JvmVal)
    (cSt : CalculatorState) (r : CheckedEvalResult) (hf : 30 ≤ f) (hpc : pc = 79)
    (hin : instrs = List.drop 79 CalculatorEngineKt_reduceCalculatorState_prog)
    (h0 : locs 0 = .ext (.calcState cSt))
    (herr : cSt.error = none) (hent : cSt.enteringNewNumber = false)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) :
    let out := match r with
      | .error e => { cSt with error := some e, enteringNewNumber := false }
      | .value v => { cSt with displayValue := v, enteringNewNumber := false, error := none }
    ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d3 + 1 + 2) subFuel) f CalculatorEngineKt_reduceCalculatorState_prog
          pc instrs ⟨pc, [.ext (.evalRes r)], locs, jh, hp⟩ =
        some (.ext (.calcState out), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  have hloc : locs = setLocal locs 0 (.ext (.calcState cSt)) := by
    funext i; cases i with | zero => exact h0 | succ _ => rfl
  intro out
  subst hpc; subst hin
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply exists_run_step
  · have hst : (⟨79, [.ext (.evalRes r)], locs, jh, hp⟩ : JvmState) =
        ⟨79, [.ext (.evalRes r)], setLocal locs 0 (.ext (.calcState cSt)), jh, hp⟩ :=
      congrArg (fun l : Nat → JvmVal => (⟨79, [.ext (.evalRes r)], l, jh, hp⟩ : JvmState)) hloc
    rw [hst]
    conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog, List.drop]
    calc_step_blk
    unfold holdOpt
    rfl
  · cases r
    case error e =>
      apply exists_run_done
      calc_io
      calc_branch
      calc_step_blk
      calc_cc
      calc_iv
      calc_step_blk
      calc_cd
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
      rw [hent]
    case value v =>
      apply exists_run_done
      calc_io
      calc_branch
      calc_norm_run_args
      calc_step_blk
      calc_io
      calc_branch
      calc_step_blk
      calc_cc
      calc_iv
      calc_step_blk
      calc_cd
      calc_step_blk
      rw [runJvmResFast_areturn_calc]
      repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
      rw [int64_toUInt64_toInt64, herr, hent]

private theorem reduceOp_fallback_equiv (resolveProg : String → Option (List JvmInstr))
    (d3 subFuel f pc : Nat) (instrs : List JvmInstr) (locs : Nat → JvmVal)
    (cSt : CalculatorState) (o : CalculatorOp) (hf : 15 ≤ f) (hpc : pc = 204)
    (hin : instrs = List.drop 204 CalculatorEngineKt_reduceCalculatorState_prog)
    (h0 : locs 0 = .ext (.calcState cSt)) (h1 : locs 1 = .ext (.calcKey (.op o)))
    (herr : cSt.error = none) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) :
    let out : CalculatorState :=
      CalculatorState.mk cSt.displayValue (some cSt.displayValue) (some o) true none
    ∃ endSt,
      Jvm.runJvmResFast (mkCalcHooks resolveProg (d3 + 2 + 1) subFuel) f CalculatorEngineKt_reduceCalculatorState_prog
          pc instrs ⟨pc, [], locs, jh, hp⟩ =
        some (.ext (.calcState out), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  have hloc : locs = setLocal (setLocal locs 0 (.ext (.calcState cSt))) 1 (.ext (.calcKey (.op o))) := by
    funext i
    cases i with
    | zero => exact h0
    | succ i =>
      cases i with
      | zero => exact h1
      | succ _ => rfl
  intro out
  subst hpc; subst hin
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hst : (⟨204, [], locs, jh, hp⟩ : JvmState) =
      ⟨204, [], setLocal (setLocal locs 0 (.ext (.calcState cSt))) 1 (.ext (.calcKey (.op o))), jh, hp⟩ :=
    congrArg (fun l : Nat → JvmVal => (⟨204, [], l, jh, hp⟩ : JvmState)) hloc
  rw [hst]
  apply exists_run_done
  conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog, List.drop]
  calc_step_blk
  calc_iv
  rw [runJvmResFast_longValueOf]
  calc_step_blk
  calc_cc
  calc_iv
  calc_step_blk
  calc_cd
  calc_step_blk
  rw [runJvmResFast_areturn_calc]
  repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
  rw [herr, int64_toUInt64_toInt64]
  rfl

macro "calc_ite_split" : tactic => `(tactic| (
  try (first
    | rw [ite_eq_left (by decide)]
    | rw [ite_eq_right (by decide)]
    | rw [ite_isNull_boxedLong]
    | rw [ite_isNull_ext]
    | rw [ite_isNull_null]
    | rw [ite_match_err]
    | rw [ite_match_val]
    | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null]))
  try (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
               simp only [Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte])))

private theorem reduceClear_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey .clear))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt .clear)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kf, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_done
  conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog]
  calc_step_blk
  rw [runJvmResFast_checkNotNullParameter (by rfl)]
  calc_step_blk
  rw [runJvmResFast_checkNotNullParameter (by rfl)]
  calc_step_blk
  calc_io
  calc_branch
  calc_step_blk
  rw [runJvmResFast_getstatic_clean (hw.staticsClean _ _ (by decide) (by decide)) rfl]
  calc_iv
  rw [runJvmResFast_areturn_calc]
  rfl

private theorem reduceDigit_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsEngineProgs resolveProg)
    (depth subFuel fuel : Nat) (hd : 3 ≤ depth) (hsub : 60 ≤ subFuel) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (d : UInt32) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg depth subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey (.digit d)))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt (.digit d))), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kf, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    calc_io
    calc_branch
    calc_norm_run_args
    calc_step_blk
    calc_iv
    calc_branch
    unfold holdOpt
    rfl
  · cases herr : cSt.error
    case some e =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_some, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        apply exists_run_done
        calc_step_blk
        rw [runJvmResFast_areturn_calc]
    case none =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        calc_norm_run_args
        apply exists_run_step
        · calc_step_blk
          calc_io
          calc_branch
          calc_step_blk
          calc_cc
          calc_iv
          calc_step_blk
          rw [i2l_to_int32_int64 d]
          calc_iv
          calc_branch
          unfold holdOpt
          rfl
        · cases hent : cSt.enteringNewNumber
          · calc_ite_split
            calc_norm_run_args
            apply exists_run_step
            · calc_step_blk
              calc_iv
              calc_step_blk
              rw [show (10 : UInt64) = Int64.toUInt64 10 from rfl]
              (conv => lhs; arg 1; arg 2; change d3 + 1 + 2)
              rw [runJvmResFast_invokestatic_checkedBin "checkedMul" CalculatorEngineKt_checkedMul_prog
                (checkedMulModel cSt.displayValue 10) (Or.inr (Or.inr (Or.inl rfl))) (hext _ _ rfl)
                (checkedMul_equiv resolveProg (d3 + 2) subFuel subFuel (by omega) hsub
                  cSt.displayValue 10 hp jh hw.staticsClean)]
              calc_step_blk
              rw [runJvmResFast_instanceof_lit
                (evalResTag (checkedMulModel cSt.displayValue 10)) (by
                cases hcm : checkedMulModel cSt.displayValue 10 <;>
                dsimp only [Jvm.stepInstr, Jvm.evalInstanceOf, mkCalcHooks, evalResTag] <;>
                unfold_calc_priv <;> rfl)]
              calc_branch
              unfold holdOpt
              rfl
            · cases hcm : checkedMulModel cSt.displayValue 10
              case error e =>
                calc_ite_split
                apply exists_run_done
                calc_step_blk
                calc_cc
                calc_iv
                calc_step_blk
                calc_cd
                calc_step_blk
                rw [runJvmResFast_areturn_calc]
                repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
                simp only [hent]
                rfl
              case value mul =>
                calc_ite_split
                calc_norm_run_args
                apply exists_run_step
                · calc_step_blk
                  calc_io
                  calc_branch
                  calc_step_blk
                  calc_iv
                  calc_step_blk
                  calc_branch
                  unfold holdOpt
                  rfl
                · apply exists_run_ite
                  · intro hge
                    rw [lcmp_ifge_iff_nslt] at hge
                    (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                             simp only [show cSt.displayValue.toBitVec.slt 0#64 = false from hge,
                               Bool.false_eq_true, ↓reduceIte])
                    calc_norm_run_args
                    apply exists_run_step
                    · calc_step_blk
                      calc_cc
                      calc_iv
                      calc_step_blk
                      (conv => lhs; arg 1; arg 2; change d3 + 1 + 2)
                      rw [runJvmResFast_invokestatic_checkedBin "checkedAdd" CalculatorEngineKt_checkedAdd_prog
                        (checkedAddModel mul (Int32.ofInt d.toBitVec.toInt).toInt64) (Or.inl rfl)
                        (hext _ _ rfl)
                        (checkedAdd_equiv resolveProg (d3 + 2) subFuel subFuel (by omega) (by omega)
                          mul (Int32.ofInt d.toBitVec.toInt).toInt64 hp jh hw.staticsClean)]
                      unfold holdOpt
                      rfl
                    · refine reduceDigit_finish_equiv resolveProg d3 subFuel _ _ _ _ cSt
                        (checkedAddModel mul (Int32.ofInt d.toBitVec.toInt).toInt64) ?_ ?_ ?_ ?_ herr hent hp jh
                      · try simp only [Nat.add_eq]
                        omega
                      · rfl
                      · dsimp only [CalculatorEngineKt_reduceCalculatorState_prog, List.drop]; try rfl
                      · rfl
                  · intro hge
                    rw [lcmp_ifge_iff_nslt] at hge
                    have hslt : cSt.displayValue.toUInt64.toBitVec.slt 0#64 = true := by
                      cases hs : cSt.displayValue.toUInt64.toBitVec.slt 0#64
                      · exact absurd hs hge
                      · rfl
                    (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                             simp only [show cSt.displayValue.toBitVec.slt 0#64 = true from hslt, ↓reduceIte])
                    apply exists_run_step
                    · calc_step_blk
                      calc_cc
                      calc_iv
                      calc_step_blk
                      (conv => lhs; arg 1; arg 2; change d3 + 1 + 2)
                      rw [runJvmResFast_invokestatic_checkedBin "checkedSub" CalculatorEngineKt_checkedSub_prog
                        (checkedSubModel mul (Int32.ofInt d.toBitVec.toInt).toInt64)
                        (Or.inr (Or.inl rfl)) (hext _ _ rfl)
                        (checkedSub_equiv resolveProg (d3 + 2) subFuel subFuel (by omega) (by omega)
                          mul (Int32.ofInt d.toBitVec.toInt).toInt64 hp jh hw.staticsClean)]
                      calc_branch
                      unfold holdOpt
                      rfl
                    · refine reduceDigit_finish_equiv resolveProg d3 subFuel _ _ _ _ cSt
                        (checkedSubModel mul (Int32.ofInt d.toBitVec.toInt).toInt64) ?_ ?_ ?_ ?_ herr hent hp jh
                      · try simp only [Nat.add_eq]
                        omega
                      · rfl
                      · dsimp only [CalculatorEngineKt_reduceCalculatorState_prog, List.drop]; try rfl
                      · rfl
          · calc_ite_split
            apply exists_run_done
            calc_step_blk
            calc_cd
            calc_step_blk
            rw [runJvmResFast_areturn_calc]
            repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
            simp only [int64_toUInt64_toInt64, herr]
            rfl

private theorem reduceBackspace_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey .backspace))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt .backspace)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kf, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    calc_io
    calc_branch
    calc_norm_run_args
    calc_step_blk
    calc_iv
    calc_branch
    unfold holdOpt
    rfl
  · cases herr : cSt.error
    case some e =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_some, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        apply exists_run_done
        calc_step_blk
        rw [runJvmResFast_areturn_calc]
    case none =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        calc_norm_run_args
        apply exists_run_step
        · calc_step_blk
          calc_io
          calc_branch
          calc_norm_run_args
          calc_step_blk
          rw [runJvmResFast_getstatic_clean (hw.staticsClean _ _ (by decide) (by decide)) rfl]
          rw [runJvmResFast_areEqual_step (by rfl)]
          calc_branch
          calc_step_blk
          calc_iv
          calc_branch
          unfold holdOpt
          rfl
        · cases hent : cSt.enteringNewNumber
          · calc_ite_split
            calc_norm_run_args
            apply exists_run_done
            calc_step_blk
            calc_iv
            calc_step_blk
            rw [runJvmResFast_ldiv (by decide)]
            calc_step_blk
            calc_cd
            calc_step_blk
            rw [runJvmResFast_areturn_calc]
            repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
            rw [show (UInt64.toInt64 10 : Int64) = 10 by decide, herr, hent]
            repeat rw [int64_toUInt64_toInt64]
          · calc_ite_split
            apply exists_run_done
            calc_step_blk
            rw [runJvmResFast_areturn_calc]

set_option maxRecDepth 2048 in
private theorem reduceOp_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsEngineProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsub : 60 ≤ subFuel) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (o : CalculatorOp) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey (.op o)))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt (.op o))), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kf, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    calc_io
    calc_branch
    calc_norm_run_args
    calc_step_blk
    calc_iv
    calc_branch
    unfold holdOpt
    rfl
  · cases herr : cSt.error
    case some e =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_some, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        apply exists_run_done
        calc_step_blk
        rw [runJvmResFast_areturn_calc]
    case none =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        calc_norm_run_args
        apply exists_run_step
        · calc_step_blk
          calc_io
          calc_branch
          calc_norm_run_args
          calc_step_blk
          rw [runJvmResFast_getstatic_clean (hw.staticsClean _ _ (by decide) (by decide)) rfl]
          rw [runJvmResFast_areEqual_step (res := false) (by cases o <;> rfl)]
          calc_branch
          calc_norm_run_args
          calc_step_blk
          calc_io
          calc_branch
          calc_step_blk
          calc_iv
          calc_step_blk
          calc_iv
          calc_step_blk
          unfold holdOpt
          rfl
        · cases hpop : cSt.pendingOperand <;> cases hpo : cSt.pendingOp
          · apply exists_run_step
            · calc_branch
              calc_norm_run_args
              unfold holdOpt
              rfl
            · refine reduceOp_fallback_equiv resolveProg d3 subFuel _ _ _ _ cSt o ?_ rfl rfl ?_ ?_ herr hp jh
              · try simp only [Nat.add_eq]; omega
              · rfl
              · rfl
          · apply exists_run_step
            · calc_branch
              calc_norm_run_args
              unfold holdOpt
              rfl
            · refine reduceOp_fallback_equiv resolveProg d3 subFuel _ _ _ _ cSt o ?_ rfl rfl ?_ ?_ herr hp jh
              · try simp only [Nat.add_eq]; omega
              · rfl
              · rfl
          · apply exists_run_step
            · calc_branch
              calc_step_blk
              calc_branch
              calc_norm_run_args
              unfold holdOpt
              rfl
            · refine reduceOp_fallback_equiv resolveProg d3 subFuel _ _ _ _ cSt o ?_ rfl rfl ?_ ?_ herr hp jh
              · try simp only [Nat.add_eq]; omega
              · rfl
              · rfl
          · simp only
            cases hent : cSt.enteringNewNumber
            · calc_ite_split
              apply exists_run_step
              · calc_branch
                calc_step_blk
                calc_branch
                calc_step_blk
                calc_iv
                rw [hent]
                calc_branch
                calc_step_blk
                calc_iv
                calc_step_blk
                calc_iv
                rw [runJvmResFast_invokestatic_applyOp (by decide) (hext _ _ rfl)
                  (applyOp_equiv resolveProg hext (d3 + 2) subFuel subFuel (by omega) hsub (by omega)
                    _ _ _ hp jh hw)]
                calc_step_blk
                rw [runJvmResFast_instanceof_lit
                  (evalResTag (applyOpModel _ _ cSt.displayValue)) (by
                  cases haop : applyOpModel _ _ cSt.displayValue <;>
                  dsimp only [Jvm.stepInstr, Jvm.evalInstanceOf, mkCalcHooks, evalResTag] <;>
                  unfold_calc_priv <;> rfl)]
                calc_branch
                unfold holdOpt
                rfl
              · cases haop : applyOpModel _ _ cSt.displayValue
                case error e =>
                  (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1; dsimp only)
                  calc_ite_split
                  apply exists_run_done
                  calc_step_blk
                  calc_cc
                  calc_iv
                  calc_step_blk
                  calc_cd
                  calc_step_blk
                  rw [runJvmResFast_areturn_calc]
                  repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
                  try rw [int64_toUInt64_toInt64]
                  try rw [herr]
                  try rw [hent]
                  try rw [show ((0 : UInt32) != 0) = false by decide]
                  try rw [show ((1 : UInt32) != 0) = true by decide]
                  try rfl
                case value v =>
                  (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1; dsimp only)
                  calc_ite_split
                  calc_norm_run_args
                  apply exists_run_done
                  calc_step_blk
                  calc_io
                  calc_branch
                  calc_step_blk
                  calc_cc
                  calc_iv
                  calc_step_blk
                  calc_cc
                  calc_iv
                  rw [runJvmResFast_longValueOf]
                  calc_step_blk
                  calc_cc
                  calc_iv
                  calc_step_blk
                  calc_cd
                  calc_step_blk
                  rw [runJvmResFast_areturn_calc]
                  repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
                  try rw [int64_toUInt64_toInt64]
                  try rw [herr]
                  try rw [hent]
                  try rw [show ((0 : UInt32) != 0) = false by decide]
                  try rw [show ((1 : UInt32) != 0) = true by decide]
                  try rfl
            · calc_ite_split
              apply exists_run_step
              · calc_branch
                calc_step_blk
                calc_branch
                calc_step_blk
                calc_iv
                rw [hent]
                calc_branch
                calc_norm_run_args
                unfold holdOpt
                rfl
              · refine reduceOp_fallback_equiv resolveProg d3 subFuel _ _ _ _ cSt o ?_ rfl rfl ?_ ?_ herr hp jh
                · try simp only [Nat.add_eq]; omega
                · rfl
                · rfl

set_option maxRecDepth 2048 in
private theorem reduceEquals_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsEngineProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsub : 60 ≤ subFuel) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey .equals))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt .equals)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kf, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runJvmRes_exists_fast0 rfl
  apply exists_run_step
  · conv => lhs; arg 5; dsimp only [CalculatorEngineKt_reduceCalculatorState_prog]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    rw [runJvmResFast_checkNotNullParameter (by rfl)]
    calc_step_blk
    calc_io
    calc_branch
    calc_norm_run_args
    calc_step_blk
    calc_iv
    calc_branch
    unfold holdOpt
    rfl
  · cases herr : cSt.error
    case some e =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_some, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        apply exists_run_done
        calc_step_blk
        rw [runJvmResFast_areturn_calc]
    case none =>
        (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                 dsimp only [reduceCalculatorStateModel]
                 simp only [herr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte])
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        | (dsimp only; first | rw [ite_isNull_ext] | rw [ite_isNull_null])
        calc_norm_run_args
        apply exists_run_step
        · calc_step_blk
          calc_io
          calc_branch
          calc_norm_run_args
          calc_step_blk
          rw [runJvmResFast_getstatic_clean (hw.staticsClean _ _ (by decide) (by decide)) rfl]
          rw [runJvmResFast_areEqual_step (by rfl)]
          calc_branch
          calc_norm_run_args
          calc_step_blk
          calc_io
          calc_branch
          calc_norm_run_args
          calc_step_blk
          rw [runJvmResFast_getstatic_clean (hw.staticsClean _ _ (by decide) (by decide)) rfl]
          rw [runJvmResFast_areEqual_step (by rfl)]
          calc_branch
          calc_step_blk
          calc_iv
          calc_step_blk
          calc_iv
          calc_step_blk
          unfold holdOpt
          rfl
        · cases hpop : cSt.pendingOperand <;> cases hpo : cSt.pendingOp
          · apply exists_run_done
            calc_branch
            calc_norm_run_args
            calc_step_blk
            calc_cd
            calc_step_blk
            rw [runJvmResFast_areturn_calc]
            repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
            rw [herr, hpop, hpo, show ((1 : UInt32) != 0) = true by decide]
          · apply exists_run_done
            calc_branch
            calc_norm_run_args
            calc_step_blk
            calc_cd
            calc_step_blk
            rw [runJvmResFast_areturn_calc]
            repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
            rw [herr, hpop, hpo, show ((1 : UInt32) != 0) = true by decide]
          · apply exists_run_done
            calc_branch
            calc_step_blk
            calc_branch
            calc_norm_run_args
            calc_step_blk
            calc_cd
            calc_step_blk
            rw [runJvmResFast_areturn_calc]
            repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
            rw [herr, hpop, hpo, show ((1 : UInt32) != 0) = true by decide]
          · apply exists_run_step
            · calc_branch
              calc_step_blk
              calc_branch
              calc_step_blk
              calc_iv
              calc_step_blk
              calc_iv
              rw [runJvmResFast_invokestatic_applyOp (by decide) (hext _ _ rfl)
                (applyOp_equiv resolveProg hext (d3 + 2) subFuel subFuel (by omega) hsub (by omega)
                  _ _ _ hp jh hw)]
              calc_step_blk
              rw [runJvmResFast_instanceof_lit
                (evalResTag (applyOpModel _ _ cSt.displayValue)) (by
                cases haop : applyOpModel _ _ cSt.displayValue <;>
                dsimp only [Jvm.stepInstr, Jvm.evalInstanceOf, mkCalcHooks, evalResTag] <;>
                unfold_calc_priv <;> rfl)]
              calc_branch
              unfold holdOpt
              rfl
            · cases haop : applyOpModel _ _ cSt.displayValue
              case error e =>
                (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                         dsimp only; try rw [haop]; dsimp only)
                calc_ite_split
                apply exists_run_done
                rw [runJvmResFast_newClass_calc (by decide)]
                calc_step_blk
                calc_cc
                calc_iv
                calc_step_blk
                calc_cs
                calc_step_blk
                rw [runJvmResFast_areturn_calc]
                repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
                try rw [int64_toUInt64_toInt64]
                try rw [herr]
                try rw [show ((0 : UInt32) != 0) = false by decide]
                try rw [show ((1 : UInt32) != 0) = true by decide]
                try rfl
              case value v =>
                (conv => arg 1; intro endSt; arg 1; rhs; arg 1; arg 1; arg 1; arg 1
                         dsimp only; try rw [haop]; dsimp only)
                calc_ite_split
                calc_norm_run_args
                apply exists_run_done
                calc_step_blk
                calc_io
                calc_branch
                rw [runJvmResFast_newClass_calc (by decide)]
                calc_step_blk
                calc_cc
                calc_iv
                calc_step_blk
                calc_cs
                calc_step_blk
                rw [runJvmResFast_areturn_calc]
                repeat (first | rw [u32_and_ite_t (by decide)] | rw [u32_and_ite_f (by decide)])
                try rw [int64_toUInt64_toInt64]
                try rw [herr]
                try rw [show ((0 : UInt32) != 0) = false by decide]
                try rw [show ((1 : UInt32) != 0) = true by decide]
                try rfl

theorem reduceCalculatorState_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsEngineProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsub : 60 ≤ subFuel) (hf : 80 ≤ fuel)
    (cSt : CalculatorState) (k : CalculatorKey) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks resolveProg d subFuel) fuel CalculatorEngineKt_reduceCalculatorState_prog
        (initCalcJvmState [(0, .ext (.calcState cSt)), (1, .ext (.calcKey k))] hp jh) =
        some (.ext (.calcState (reduceCalculatorStateModel cSt k)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  cases k with
  | clear => exact reduceClear_equiv resolveProg d subFuel fuel hd hf cSt hp jh hw
  | digit dig => exact reduceDigit_equiv resolveProg hext d subFuel fuel hd hsub hf cSt dig hp jh hw
  | backspace => exact reduceBackspace_equiv resolveProg d subFuel fuel hd hf cSt hp jh hw
  | op o => exact reduceOp_equiv resolveProg hext d subFuel fuel hd hsub hf cSt o hp jh hw
  | equals => exact reduceEquals_equiv resolveProg hext d subFuel fuel hd hsub hf cSt hp jh hw

end MosaicCalculator.KotlinJvmVerification

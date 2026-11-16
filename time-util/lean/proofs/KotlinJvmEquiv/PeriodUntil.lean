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

namespace TimeUtil.KotlinJvmVerification

open TimeUtil.JvmVerification
open TimeUtil.KotlinJvmBytecode
open TimeUtil.Model

/-! ### Program Lookup Table, Hooks, and Clean Static Heap Invariant -/

/-- Bytecode lookup table for all `PeriodUntilKt` methods, indexed by `(utf8ByteSize, back)` for O(1) reduction. -/
def timeProgLookup (fnTag : String) : Option (List JvmInstr) :=
  if fnTag = "PeriodUntilKt.getTotalNanoseconds:(Lkotlinx/datetime/DateTimePeriod;)J" then
    some PeriodUntilKt_getTotalNanoseconds_prog
  else if fnTag = "PeriodUntilKt.getApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" then
    some PeriodUntilKt_getApproximateDuration_prog
  else if fnTag = "PeriodUntilKt.getTimeComponentDuration:(Lkotlinx/datetime/DateTimePeriod;)J" then
    some PeriodUntilKt_getTimeComponentDuration_prog
  else if fnTag = "PeriodUntilKt.getApproximateDurationInMinutes:(Lkotlinx/datetime/DateTimePeriod;)D" then
    some PeriodUntilKt_getApproximateDurationInMinutes_prog
  else if fnTag = "PeriodUntilKt.getDateComponentApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" then
    some PeriodUntilKt_getDateComponentApproximateDuration_prog
  else if fnTag = "PeriodUntilKt.dateComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I" then
    some PeriodUntilKt_dateComponentInWholeUnits_prog
  else if fnTag = "PeriodUntilKt.timeComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" then
    some PeriodUntilKt_timeComponentInWholeUnits_prog
  else if fnTag = "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;)Lkotlin/Pair;" then
    some PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog
  else if fnTag = "PeriodUntilKt.progressivePeriodUntil:(Lkotlin/time/Instant;Lkotlin/time/Clock;Ljava/util/List;Landroidx/compose/runtime/Composer;I)Lkotlin/Pair;" then
    some PeriodUntilKt_progressivePeriodUntil_1_prog
  else if fnTag = "PeriodUntilKt.periodUntilWithProgressiveUnits:(Lkotlin/time/Instant;Lkotlin/time/Instant;Ljava/util/List;Lkotlinx/datetime/TimeZone;)Lkotlin/Pair;" then
    some PeriodUntilKt_periodUntilWithProgressiveUnits_prog
  else if fnTag = "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;" then
    some PeriodUntilKt_periodUntilWithUnit_1_prog
  else if fnTag = "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;" then
    some PeriodUntilKt_periodUntilWithUnit_prog
  else if fnTag = "PeriodUntilKt.progressivePeriodUntil:(Lkotlin/time/Instant;Lkotlin/time/Clock;Ljava/util/List;Lkotlinx/datetime/TimeZone;Landroidx/compose/runtime/Composer;I)Lkotlin/Pair;" then
    some PeriodUntilKt_progressivePeriodUntil_prog
  else if fnTag = "PeriodUntilKt.periodUntil:(Lkotlin/time/Instant;Lkotlin/time/Clock;Lkotlinx/datetime/DateTimeUnit$TimeBased;Landroidx/compose/runtime/Composer;I)Lkotlinx/datetime/DateTimePeriod;" then
    some PeriodUntilKt_periodUntil_1_prog
  else if fnTag = "PeriodUntilKt.periodUntil:(Lkotlin/time/Instant;Lkotlin/time/Clock;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;Landroidx/compose/runtime/Composer;I)Lkotlinx/datetime/DateTimePeriod;" then
    some PeriodUntilKt_periodUntil_prog
  else none

/-- Predicate asserting `resolveProg` extends `timeProgLookup`. -/
def ExtendsTimeProgs (resolveProg : String → Option (List JvmInstr)) : Prop :=
  ∀ fnTag prog, timeProgLookup fnTag = some prog → resolveProg fnTag = some prog

theorem timeProgLookup_extends : ExtendsTimeProgs timeProgLookup :=
  fun _ _ h => h

/-- Predicate asserting no `Duration`/`DurationUnit`/`Composer` static fields are overridden in `jh`. -/
def HasTimeStaticsClean (jh : Jvm.JvmHeap TimeExt) : Prop :=
  ∀ cls fld, jh.getStatic? cls fld = none

theorem emptyJvmHeap_staticsClean : HasTimeStaticsClean ({} : Jvm.JvmHeap TimeExt) :=
  fun _ _ => rfl

instance (resolveProg : String → Option (List JvmInstr)) (d fuel : Nat) :
    Jvm.HasDefaultIsZero (mkTimeHooks resolveProg d fuel) where
  isZero?_eq := by cases d <;> rfl

/-! ### Fast Symbolic Block Stepper & Tactics -/

/-- Stop predicate for `stepBlockChunkWith`: halts on invokes, statics, allocs, casts, div, throws, returns, branches. -/
def isTimeStop : JvmInstr → Bool
  | .invokestatic _ _ _ | .invokevirtual _ _ _ | .invokespecial _ _ _ | .invokeinterface _ _ _
  | .invokedynamic _ _ _ | .getstatic _ _ _ | .putstatic _ _ _ | .getfield _ _ _ | .putfield _ _ _
  | .newClass _ | .checkcast _ | .instanceof _ | .idiv | .ldiv | .athrow
  | .areturn | .ireturn | .lreturn | .freturn | .dreturn | .vreturn
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .goto _ | .tableswitch _ _ _ | .lookupswitch _ _ => true
  | _ => false

section StepTactics

open Lean Elab Tactic Meta

def timeOpaqueConsts : NameSet :=
  NameSet.empty
    |>.insert ``mkTimeHooks
    |>.insert ``timeProgLookup
    |>.insert ``PeriodUntilKt_getTotalNanoseconds_prog
    |>.insert ``PeriodUntilKt_dateComponentInWholeUnits_prog
    |>.insert ``PeriodUntilKt_timeComponentInWholeUnits_prog
    |>.insert ``PeriodUntilKt_getTimeComponentDuration_prog
    |>.insert ``PeriodUntilKt_getDateComponentApproximateDuration_prog
    |>.insert ``PeriodUntilKt_getApproximateDuration_prog
    |>.insert ``PeriodUntilKt_getApproximateDurationInMinutes_prog
    |>.insert ``PeriodUntilKt_periodUntilWithUnit_prog
    |>.insert ``PeriodUntilKt_periodUntilWithUnit_1_prog
    |>.insert ``PeriodUntilKt_periodUntilWithProgressiveUnits_prog
    |>.insert ``PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog
    |>.insert ``PeriodUntilKt_periodUntil_prog
    |>.insert ``PeriodUntilKt_periodUntil_1_prog
    |>.insert ``PeriodUntilKt_progressivePeriodUntil_prog
    |>.insert ``PeriodUntilKt_progressivePeriodUntil_1_prog
    |>.insert ``Model.totalNanosecondsModel
    |>.insert ``Model.dateComponentInWholeUnitsModel
    |>.insert ``Model.timeComponentInWholeUnitsModel
    |>.insert ``Model.timeComponentDurationModel
    |>.insert ``Model.dateComponentApproximateDurationModel
    |>.insert ``Model.approximateDurationModel
    |>.insert ``Model.approximateDurationInMinutesModel
    |>.insert ``Model.periodUntilWithUnitModel
    |>.insert ``Model.periodUntilWithUnitTimeModel
    |>.insert ``Model.periodUntilWithProgressiveUnitsModel
    |>.insert ``Model.periodUntilWithProgressiveUnitsTimeModel
    |>.insert ``Model.Duration.ofIntUnit
    |>.insert ``Model.Duration.ofLongUnit
    |>.insert ``Model.Duration.ofDaysFloat?
    |>.insert ``Model.Duration.ofDaysFloat
    |>.insert ``Model.Duration.inWholeNanoseconds
    |>.insert ``Model.Duration.plus?
    |>.insert ``Model.Duration.plus
    |>.insert ``Model.DateTimePeriodModel.ofNanoseconds
    |>.insert ``Model.DateTimePeriodModel.ofDays
    |>.insert ``Model.DateTimePeriodModel.ofMonths
    |>.insert ``Model.jvmI32Div
    |>.insert ``Model.jvmI64Div
    |>.insert ``Jvm.i64ToFloat
    |>.insert ``Jvm.i32ToFloat
    |>.insert ``Jvm.floatToI64
    |>.insert ``Compose.startMovableGroup
    |>.insert ``Compose.endMovableGroup
    |>.insert ``Compose.checkChangedSlot
    |>.insert ``Compose.readRememberSlot
    |>.insert ``Compose.writeRememberSlot
    |>.insert ``Compose.allocState
    |>.insert ``Compose.readState

def timeInitConsts : List Name :=
  [``initTimeJvmState, ``Jvm.initJvmState]

elab "time_whnf_blk" : conv => withMainContext do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let res ← Jvm.Tactics.withOpaque timeOpaqueConsts
    (Jvm.Tactics.normJvmBlkExpr timeInitConsts (fun _ => pure none) lhs)
  Lean.Elab.Tactic.Conv.changeLhs res

elab "time_norm_locals" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let res ← Jvm.Tactics.normJvmLocalsExpr timeInitConsts (fun _ => pure none) [] tgt
    return [← g.replaceTargetDefEq res]

elab "time_norm_run_args" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← instantiateMVars (← g.getType)
    let normSt := fun s : Expr => do
      let s1 ← Jvm.Tactics.withOpaque timeOpaqueConsts
        (Jvm.Tactics.normJvmBlkExpr timeInitConsts (fun _ => pure none) s)
      if s1.isAppOfArity ``Jvm.JvmState.mk 7 then
        let sa := s1.getAppArgs
        let pcField ← Jvm.Tactics.normJvmNatWith timeOpaqueConsts sa[2]!
        return mkAppN s1.getAppFn #[sa[0]!, sa[1]!, pcField, sa[3]!, sa[4]!, sa[5]!, sa[6]!]
      else
        return s1
    let normRun := fun b : Expr => do
      if b.isAppOfArity ``Jvm.runJvmResFast 8 then
        let ba := b.getAppArgs
        let fuel' ← Jvm.Tactics.withOpaque timeOpaqueConsts (whnf ba[3]!)
        let pc' ← Jvm.Tactics.withOpaque timeOpaqueConsts (whnf ba[5]!)
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

def isTimeNonStop : TacticM Bool := do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Jvm.runJvmResFast 8 then
    let instrs ← whnf (lhs.getArg! 6)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← whnf (mkApp (mkConst ``isTimeStop) instr)
      return br.isConstOf ``Bool.false
  return false

def isTimeForwardGoto : TacticM Bool := do
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

elab "time_step_one_chunk" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then return ()
  evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_stepBlockChunkWith _ isTimeStop 64]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (conv => lhs; arg 2; time_whnf_blk)))
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
      evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_locals)))
      evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_run_args)))

elab "time_step_blk" : tactic => do
  for _ in [:40] do
    if (← getUnsolvedGoals).isEmpty then break
    if ← isTimeNonStop then
      evalTactic (← `(tactic| time_step_one_chunk))
    else if ← isTimeForwardGoto then
      evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_run_args)))
      evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (
          (conv => lhs; arg 2; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 5; whnf)
          (conv => lhs; arg 7; time_whnf_blk))))
        let tgt2 := (← getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
        if !(← getUnsolvedGoals).isEmpty then
          evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_locals; time_norm_run_args)))
    else
      break

elab "time_branch" : tactic => do
  let tgt := (← getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | throwError "time_branch: goal is not an equation"
  let lhs := lhs.consumeMData
  if !lhs.isAppOfArity ``Jvm.runJvmResFast 8 then throwError "time_branch: not a fast JVM run"
  evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_run_args)))
  evalTactic (← `(tactic| rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]))
  if !(← getUnsolvedGoals).isEmpty then
    evalTactic (← `(tactic| (
      (conv => lhs; arg 2; whnf)
      (conv => lhs; arg 4; whnf)
      (conv => lhs; arg 5; whnf)
      (conv => lhs; arg 7; time_whnf_blk))))
    let tgt2 := (← getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    Jvm.Tactics.rwEvalBranchByInstrWith Jvm.Tactics.defaultEvalBranchThm true (lhs2.consumeMData.getArg! 6)
    if !(← getUnsolvedGoals).isEmpty then
      evalTactic (← `(tactic| try (first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)])))
      if !(← getUnsolvedGoals).isEmpty then
        evalTactic (← `(tactic| (conv => lhs; tactic => time_norm_locals; time_norm_run_args)))

/-- Steps one stop instruction whose hook result is computed by `rfl`, then continues with `time_step_blk`. -/
macro "time_rfl_step" : tactic => `(tactic| (
  first
    | rw [Jvm.runJvmResFast_invokestatic_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokeinterface_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    | rw [Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) (by rfl) rfl]
  time_step_blk))

end StepTactics

/-! ### Domain Step & Helper Lemmas -/

theorem runFast_exists0 {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fuel : Nat} {prog : List JvmInstr} {st0 : JvmState} {v : JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} (hpc : st0.pc = 0)
    (h : ∃ endSt, Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) fuel prog 0 prog st0 =
        some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) :
    ∃ endSt, Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel prog st0 =
        some (v, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp :=
  let ⟨endSt, h1, h2, h3⟩ := h
  ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ hpc h1, h2, h3⟩

theorem runFast_checkNotNull {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {param : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hnn : v.isNull = false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str param :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric] <;> simp [hnn]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl


theorem runFast_getstatic_clean {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls fld desc : String} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hclean : jh.getStatic? cls fld = none)
    (hres : (mkTimeHooks resolveProg d subFuel).resolveStatic ⟨pc, stk, locs, jh, hp⟩ cls fld desc = some v) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.getstatic cls fld desc :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) (.getstatic cls fld desc) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hclean, hres]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl


theorem runFast_ireturn {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ireturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .ireturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  cases d <;> rfl

theorem runFast_lreturn {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.lreturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .lreturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

theorem runFast_dreturn {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.dreturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .dreturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

theorem runFast_areturn {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.areturn :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .areturn rest
    ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

theorem runFast_goto {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.goto target :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  rfl

theorem runFast_ifeq_zero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hz : v = 0 := by decide) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifeq target :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  subst hz
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkTimeHooks resolveProg d subFuel)]

theorem runFast_ifeq_nonzero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hnz : v ≠ 0) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifeq target :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkTimeHooks resolveProg d subFuel), hnz]

theorem runFast_ifne_nonzero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hnz : v ≠ 0) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifne target :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := mkTimeHooks resolveProg d subFuel), hnz]

theorem runFast_ifnonnull_branch {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hnn : v.isNull = false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hnn]

theorem runFast_ifnonnull_fallthrough {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ifnonnull target :: rest)
        ⟨pc0, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.isNull]

theorem runFast_if_icmple_gt {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hgt : a.toBitVec.sle b.toBitVec = false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.if_icmple target :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hgt]

theorem runFast_if_acmpne_branch {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : TimeExt}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hne : beqRefTimeExt a b = some false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc
        (.if_acmpne target :: rest) ⟨pc0, .ext b :: .ext a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.refEq?]
  have hbeq : (mkTimeHooks resolveProg d subFuel).beqRefExt = beqRefTimeExt := by cases d <;> rfl
  rw [hbeq, hne]
  rfl

theorem runFast_if_acmpne_fallthrough {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : TimeExt}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (heq : beqRefTimeExt a b = some true) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc
        (.if_acmpne target :: rest) ⟨pc0, .ext b :: .ext a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkTimeHooks resolveProg d subFuel) (hbr := rfl)]
  dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.refEq?]
  have hbeq : (mkTimeHooks resolveProg d subFuel).beqRefExt = beqRefTimeExt := by cases d <;> rfl
  rw [hbeq, heq]
  rfl

theorem runFast_idiv {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : Int32} (hb : b ≠ 0)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.idiv :: rest)
        ⟨pc0, .i32 b.toUInt32 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (Model.jvmI32Div a b).toUInt32 :: stk, locs, jh, hp⟩ := by
  have hbu : (b.toUInt32 == 0) = false := by
    apply beq_false_of_ne
    intro h; apply hb
    exact Int32.toBitVec_inj.mp (by simpa using congrArg UInt32.toBitVec h)
  have hdiv : Jvm.jvmI32Div a.toUInt32 b.toUInt32 = some (Model.jvmI32Div a b).toUInt32 := by
    simp only [Jvm.jvmI32Div, hbu, Bool.false_eq_true, ↓reduceIte, Model.jvmI32Div]
    congr 1; apply UInt32.toBitVec_inj.mp
    change BitVec.sdiv a.toBitVec b.toBitVec = BitVec.ofInt 32 (BitVec.sdiv a.toBitVec b.toBitVec).toInt
    exact BitVec.ofInt_toInt.symm
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) .idiv
      ⟨pc, .i32 b.toUInt32 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (Model.jvmI32Div a b).toUInt32 :: stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.JvmVal.asI32?] <;> rw [hdiv]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl


theorem runFast_idiv_zero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a : Int32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.idiv :: rest)
        ⟨pc0, .i32 0 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ = none := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) .idiv
      ⟨pc, .i32 0 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ = .inr none := by
    cases d <;> rfl
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .idiv rest
    ⟨pc0, .i32 0 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ rfl (by simp)]
  rw [hs]

theorem runFast_ldiv {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : Int64} (hb : b ≠ 0)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ldiv :: rest)
        ⟨pc0, .i64 b.toUInt64 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (Model.jvmI64Div a b).toUInt64 :: stk, locs, jh, hp⟩ := by
  have hbu : (b.toUInt64 == 0) = false := by
    apply beq_false_of_ne
    intro h; apply hb
    exact Int64.toBitVec_inj.mp (by simpa using congrArg UInt64.toBitVec h)
  have hdiv : Jvm.jvmI64Div a.toUInt64 b.toUInt64 = some (Model.jvmI64Div a b).toUInt64 := by
    simp only [Jvm.jvmI64Div, hbu, Bool.false_eq_true, ↓reduceIte, Model.jvmI64Div]
    congr 1; apply UInt64.toBitVec_inj.mp
    change BitVec.sdiv a.toBitVec b.toBitVec = BitVec.ofInt 64 (BitVec.sdiv a.toBitVec b.toBitVec).toInt
    exact BitVec.ofInt_toInt.symm
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) .ldiv
      ⟨pc, .i64 b.toUInt64 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (Model.jvmI64Div a b).toUInt64 :: stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.JvmVal.asI64?] <;> rw [hdiv]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl


theorem runFast_ldiv_zero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a : Int64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.ldiv :: rest)
        ⟨pc0, .i64 0 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ = none := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) .ldiv
      ⟨pc, .i64 0 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ = .inr none := by
    cases d <;> rfl
  rw [Jvm.runJvmResFast_step_nonbranch (mkTimeHooks resolveProg d subFuel) f prog pc .ldiv rest
    ⟨pc0, .i64 0 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ rfl (by simp)]
  rw [hs]

theorem int32_toUInt32_toInt32 (x : Int32) : x.toUInt32.toInt32 = x := by
  cases x; rfl

theorem int64_toUInt64_toInt64 (x : Int64) : x.toUInt64.toInt64 = x := by
  cases x; rfl

theorem int32_toFloat_eq_i32ToFloat (x : Int32) :
    Jvm.i32ToFloat x.toUInt32 = x.toFloat := by
  dsimp only [Jvm.i32ToFloat]
  rw [int32_toUInt32_toInt32]

theorem int32_signExtend_i64 (d : Int32) :
    UInt64.ofBitVec (d.toUInt32.toBitVec.signExtend 64) = (Int64.ofInt d.toInt).toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toInt_eq
  change (d.toBitVec.signExtend 64).toInt = (BitVec.ofInt 64 d.toInt).toInt
  have hd1 : -(2 ^ 31 : Int) ≤ d.toInt := d.toBitVec.le_toInt
  have hd2 : d.toInt < (2 ^ 31 : Int) := d.toBitVec.toInt_lt
  rw [BitVec.toInt_signExtend, BitVec.toInt_ofInt]
  simp only [show min 64 32 = 32 from rfl]
  change d.toInt.bmod (2 ^ 32) = d.toInt.bmod (2 ^ 64)
  rw [Int.bmod_eq_of_le_mul_two (by omega) (by omega), Int.bmod_eq_of_le_mul_two (by omega) (by omega)]

theorem int64_truncate_i32 (x : Int64) :
    x.toUInt64.toUInt32.toInt32 = Int32.ofInt x.toInt := by
  apply Int32.toBitVec_inj.mp
  apply BitVec.eq_of_toInt_eq
  change (x.toBitVec.setWidth 32).toInt = (BitVec.ofInt 32 x.toBitVec.toInt).toInt
  rw [BitVec.toInt_setWidth, BitVec.toInt_ofInt]
  have hcond := BitVec.toInt_eq_toNat_cond x.toBitVec
  split at hcond
  · rw [hcond]
  · rw [hcond]
    have hmul : (↑(2 ^ 64 : Nat) : Int) = (↑(2 ^ 32 : Nat) : Int) * (↑(2 ^ 32 : Nat) : Int) := by decide
    simp only [Int.bmod_def]
    rw [hmul]
    have hmod : (↑x.toBitVec.toNat - (↑(2 ^ 32 : Nat) : Int) * (↑(2 ^ 32 : Nat) : Int)) % (↑(2 ^ 32 : Nat) : Int) =
        (↑x.toBitVec.toNat : Int) % (↑(2 ^ 32 : Nat) : Int) := by
      have hsub := Int.sub_mul_emod_self_left (↑x.toBitVec.toNat : Int) (↑(2 ^ 32 : Nat) : Int) (↑(2 ^ 32 : Nat) : Int)
      simpa [Int.mul_comm] using hsub
    rw [hmod]

theorem list_getLast_of_ne_nil {α : Type} [Inhabited α] (xs : List α) (hne : xs ≠ []) :
    xs.getLast? = some xs[xs.length - 1]! := by
  induction xs with
  | nil => contradiction
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t2 =>
      have hne2 : b :: t2 ≠ [] := List.cons_ne_nil b t2
      have h1 := ih hne2
      change (b :: t2).getLast? = some ((a :: b :: t2)[(b :: t2).length]!)
      rw [h1]
      simp

theorem stepPeriodUntilKtStatic {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel : Nat} {st : JvmState} {method desc fnTag : String} {prog : List JvmInstr}
    (tags : List Char) {args stkRest : List JvmVal} {res : JvmVal} {endSt : JvmState}
    (htags : Jvm.parseMethodParamTags desc = tags)
    (hlen : args.length = tags.length)
    (hstk : st.stack = args.reverse ++ stkRest)
    (hprog : resolveProg fnTag = some prog)
    (hrun : Jvm.runJvmRes (mkTimeHooks resolveProg d1 subFuel) subFuel prog {
        pc := 0
        stack := []
        locals := (assignParamLocalsAux 0 tags args).foldl
          (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
        jvmHeap := st.jvmHeap
        heap := st.heap
      } = some (res, endSt))
    (hfn : "PeriodUntilKt." ++ method ++ ":" ++ desc = fnTag := by simp) :
    Jvm.stepInvokeStaticGeneric (mkTimeHooks resolveProg (d1 + 1) subFuel) st
        "com/alexvanyo/composelife/timeutil/PeriodUntilKt" method desc =
      .inl (some {
        pc := st.pc + 1
        stack := res :: stkRest
        locals := st.locals
        jvmHeap := endSt.jvmHeap
        heap := endSt.heap
      }) := by
  have hnorm : (normalizeTimeClass "com/alexvanyo/composelife/timeutil/PeriodUntilKt" == "PeriodUntilKt") = true := rfl
  have hE : ∀ st' : JvmState,
      Jvm.stepInvokeStaticGeneric (mkTimeHooks resolveProg (d1 + 1) subFuel) st' "com/alexvanyo/composelife/timeutil/PeriodUntilKt" method desc =
        (mkTimeHooks resolveProg (d1 + 1) subFuel).stepInvokeStatic st' "com/alexvanyo/composelife/timeutil/PeriodUntilKt" method desc :=
    fun _ => rfl
  rw [hE]
  dsimp only [mkTimeHooks]
  rw [hnorm]
  have hcls : normalizeTimeClass "com/alexvanyo/composelife/timeutil/PeriodUntilKt" = "PeriodUntilKt" := rfl
  have hfn' : "PeriodUntilKt" ++ "." ++ method ++ ":" ++ desc = fnTag := by rw [← hfn]; rfl
  simp only [↓reduceIte, hstk, htags]
  have hlt : ¬ (args.reverse ++ stkRest).length < tags.length := by
    simp [hlen]
  have htake : ((args.reverse ++ stkRest).take tags.length).reverse = args := by
    rw [← hlen, List.take_left' (by simp), List.reverse_reverse]
  have hdrop : (args.reverse ++ stkRest).drop tags.length = stkRest := by
    rw [← hlen, List.drop_left' (by simp)]
  simp only [hlt, ↓reduceIte, htake, hdrop, hcls, hfn', hprog, hrun]

set_option maxRecDepth 4096 in
theorem tags_periodUntilWithUnit :
    Jvm.parseMethodParamTags
      "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;" =
      ['L', 'L', 'L', 'L'] := by decide

set_option maxRecDepth 4096 in
theorem tags_periodUntilWithUnit_1 :
    Jvm.parseMethodParamTags
      "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;" =
      ['L', 'L', 'L'] := by decide

set_option maxRecDepth 4096 in
theorem tags_timeComponentInWholeUnits :
    Jvm.parseMethodParamTags
      "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" =
      ['L', 'L'] := by decide

set_option maxRecDepth 4096 in
theorem tags_dateComponentInWholeUnits :
    Jvm.parseMethodParamTags
      "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I" =
      ['L', 'L'] := by decide

set_option maxRecDepth 4096 in
theorem tags_periodArg :
    Jvm.parseMethodParamTags "(Lkotlinx/datetime/DateTimePeriod;)J" = ['L'] := by decide

theorem checkInst_day_day (d : Int32) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$DayBased" (.ext (.timeUnit (.dateBased (.dayBased d)))) = true := rfl
theorem checkInst_day_month (m : Int32) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$DayBased" (.ext (.timeUnit (.dateBased (.monthBased m)))) = false := rfl
theorem checkInst_day_tb (tb : TimeBasedUnit) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$DayBased" (.ext (.timeUnit (.timeBased tb))) = false := rfl
theorem checkInst_month_month (m : Int32) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$MonthBased" (.ext (.timeUnit (.dateBased (.monthBased m)))) = true := rfl
theorem checkInst_tb_tb (tb : TimeBasedUnit) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$TimeBased" (.ext (.timeUnit (.timeBased tb))) = true := rfl
theorem checkInst_tb_db (du : DateBasedUnit) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$TimeBased" (.ext (.timeUnit (.dateBased du))) = false := rfl
theorem checkInst_db_db (du : DateBasedUnit) :
    checkTimeInstanceOf "kotlinx/datetime/DateTimeUnit$DateBased" (.ext (.timeUnit (.dateBased du))) = true := rfl

theorem runFast_instanceof_ext {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String} {e : TimeExt}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc (.instanceof cls :: rest)
        ⟨pc0, .ext e :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if checkTimeInstanceOf cls (.ext e) then 1 else 0) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.instanceof cls)
      ⟨pc, .ext e :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if checkTimeInstanceOf cls (.ext e) then 1 else 0) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_checkcast_ext {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String} {e : TimeExt}
    (hcast : checkTimeCast cls (.ext e) = some (.ext e))
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .ext e :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext e :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.checkcast cls)
      ⟨pc, .ext e :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext e :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, mkTimeHooks]
    rw [hcast]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_checkcast_null {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .null :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .null :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.checkcast cls)
      ⟨pc, .null :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .null :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_checkcast_pair {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.checkcast "kotlin/Pair")
      ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_checkcast_arrayList {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 listAddr : Nat} {cls : String} {fields : List (String × JvmVal)}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" fields))
    (hsub : Jvm.defaultIsSubtypeOf "java/util/ArrayList" cls = true := by decide) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef listAddr :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.checkcast cls)
      ⟨pc, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef listAddr :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, mkTimeHooks]
    simp only [Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hlist,
      Jvm.HeapObj.matchesType, hsub, Bool.or_true, ↓reduceIte]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_toDuration_int {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {iv : Int32} {u : DurationUnit}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/time/DurationKt" "toDuration" "(ILkotlin/time/DurationUnit;)J" :: rest)
        ⟨pc0, .ext (.durationUnit u) :: .i32 iv.toUInt32 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (Duration.ofIntUnit iv u).rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlin/time/DurationKt" "toDuration" "(ILkotlin/time/DurationUnit;)J")
      ⟨pc, .ext (.durationUnit u) :: .i32 iv.toUInt32 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (Duration.ofIntUnit iv u).rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    cases iv; cases u <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_toDuration_long {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {lv : Int64} {u : DurationUnit}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/time/DurationKt" "toDuration" "(JLkotlin/time/DurationUnit;)J" :: rest)
        ⟨pc0, .ext (.durationUnit u) :: .i64 lv.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (Duration.ofLongUnit lv u).rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlin/time/DurationKt" "toDuration" "(JLkotlin/time/DurationUnit;)J")
      ⟨pc, .ext (.durationUnit u) :: .i64 lv.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (Duration.ofLongUnit lv u).rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    cases lv; cases u <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_duration_inWholeNs {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {dur : Duration}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/time/Duration" "getInWholeNanoseconds-impl" "(J)J" :: rest)
        ⟨pc0, .i64 dur.rawValue.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 dur.inWholeNanoseconds.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlin/time/Duration" "getInWholeNanoseconds-impl" "(J)J")
      ⟨pc, .i64 dur.rawValue.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 dur.inWholeNanoseconds.toUInt64 :: stk, locs, jh, hp⟩) := by
    cases dur with | mk rv => cases rv; rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_toDuration_daysFloat {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {dv : Float} {dur : Duration}
    (hdur : Duration.ofDaysFloat? dv = some dur)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/time/DurationKt" "toDuration" "(DLkotlin/time/DurationUnit;)J" :: rest)
        ⟨pc0, .ext (.durationUnit .days) :: .f64 dv :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 dur.rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlin/time/DurationKt" "toDuration" "(DLkotlin/time/DurationUnit;)J")
      ⟨pc, .ext (.durationUnit .days) :: .f64 dv :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 dur.rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    change (match Duration.ofDaysFloat? dv with | some d => _ | none => _) = _
    rw [hdur]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_duration_plus {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {da db dc : Duration}
    (hplus : Duration.plus? da db = some dc)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/time/Duration" "plus-LRDsOJo" "(JJ)J" :: rest)
        ⟨pc0, .i64 db.rawValue.toUInt64 :: .i64 da.rawValue.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 dc.rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlin/time/Duration" "plus-LRDsOJo" "(JJ)J")
      ⟨pc, .i64 db.rawValue.toUInt64 :: .i64 da.rawValue.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 dc.rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    rcases da with ⟨⟨⟨ra⟩⟩⟩
    rcases db with ⟨⟨⟨rb⟩⟩⟩
    change (match Duration.plus? ⟨⟨⟨ra⟩⟩⟩ ⟨⟨⟨rb⟩⟩⟩ with | some d => _ | none => _) = _
    rw [hplus]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_instant_untilTz {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {start other : Int64} {u : DateTimeUnit} {tz : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/datetime/InstantKt" "until"
          "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)J" :: rest)
        ⟨pc0, .ext (.timeZone tz) :: .ext (.timeUnit u) :: .ext (.instant other) ::
          .ext (.instant start) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (hp.untilTz start other u tz).toUInt64 :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokestatic_step _ rfl

theorem runFast_instant_untilTime {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {start other : Int64} {tu : TimeBasedUnit}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/datetime/InstantKt" "until"
          "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" :: rest)
        ⟨pc0, .ext (.timeUnit (.timeBased tu)) :: .ext (.instant other) ::
          .ext (.instant start) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (hp.untilTime start other tu).toUInt64 :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokestatic_step _ rfl

theorem runFast_dateTimePeriodDefault {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {yr mon day hr min sec mask : Int32} {ns : Int64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlinx/datetime/DateTimePeriodKt" "DateTimePeriod$default"
          "(IIIIIIJILjava/lang/Object;)Lkotlinx/datetime/DateTimePeriod;" :: rest)
        ⟨pc0, .null :: .i32 mask.toUInt32 :: .i64 ns.toUInt64 :: .i32 sec.toUInt32 ::
          .i32 min.toUInt32 :: .i32 hr.toUInt32 :: .i32 day.toUInt32 ::
          .i32 mon.toUInt32 :: .i32 yr.toUInt32 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.period (applyDateTimePeriodDefault mask.toUInt32 yr.toUInt32 mon.toUInt32
          day.toUInt32 hr.toUInt32 min.toUInt32 sec.toUInt32 ns.toUInt64)) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "kotlinx/datetime/DateTimePeriodKt" "DateTimePeriod$default"
        "(IIIIIIJILjava/lang/Object;)Lkotlinx/datetime/DateTimePeriod;")
      ⟨pc, .null :: .i32 mask.toUInt32 :: .i64 ns.toUInt64 :: .i32 sec.toUInt32 ::
        .i32 min.toUInt32 :: .i32 hr.toUInt32 :: .i32 day.toUInt32 ::
        .i32 mon.toUInt32 :: .i32 yr.toUInt32 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.period (applyDateTimePeriodDefault mask.toUInt32 yr.toUInt32 mon.toUInt32
        day.toUInt32 hr.toUInt32 min.toUInt32 sec.toUInt32 ns.toUInt64)) :: stk, locs, jh, hp⟩) := by
    cases mask; cases ns; cases sec; cases min; cases hr; cases day; cases mon; cases yr; rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_tuples_to {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/TuplesKt" "to" "(Ljava/lang/Object;Ljava/lang/Object;)Lkotlin/Pair;" :: rest)
        ⟨pc0, b :: a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_invokestatic_step _ rfl

theorem runFast_math_absLong {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : Int64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "java/lang/Math" "abs" "(J)J" :: rest)
        ⟨pc0, .i64 v.toUInt64 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (if v.toUInt64.toBitVec.slt 0#64 then -v.toUInt64 else v.toUInt64) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "java/lang/Math" "abs" "(J)J")
      ⟨pc, .i64 v.toUInt64 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (if v.toUInt64.toBitVec.slt 0#64 then -v.toUInt64 else v.toUInt64) :: stk,
        locs, jh, hp⟩) := by
    cases v; rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_math_absInt {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {prog rest : List JvmInstr} {v : Int32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "java/lang/Math" "abs" "(I)I" :: rest)
        ⟨pc0, .i32 v.toUInt32 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if v.toUInt32.toBitVec.slt 0#32 then -v.toUInt32 else v.toUInt32) :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "java/lang/Math" "abs" "(I)I")
      ⟨pc, .i32 v.toUInt32 :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if v.toUInt32.toBitVec.slt 0#32 then -v.toUInt32 else v.toUInt32) :: stk,
        locs, jh, hp⟩) := by
    cases v; rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hs rfl

theorem runFast_iterator_hasNext {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 itAddr arrAddr idx : Nat} {arrCls : String} {elems : Array JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hit : jh.get? itAddr = some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]))
    (harr : jh.get? arrAddr = some (.objArray arrCls elems)) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Iterator" "hasNext" "()Z" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if (UInt32.ofNat idx).toNat < elems.size then 1 else 0) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  simp [Jvm.stepInvokeInterfaceGeneric, hit, harr]

theorem runFast_iterator_next {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 itAddr arrAddr idx : Nat} {arrCls : String} {elems : Array JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hit : jh.get? itAddr = some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]))
    (harr : jh.get? arrAddr = some (.objArray arrCls elems))
    (hlt : (UInt32.ofNat idx).toNat < elems.size) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef itAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, elems[(UInt32.ofNat idx).toNat] :: stk, locs,
          jh.set itAddr (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx + 1))]),
          hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  have hlt' : idx % 4294967296 < elems.size := by simpa [UInt32.toNat_ofNat] using hlt
  simp [Jvm.stepInvokeInterfaceGeneric, hit, harr, hlt']

theorem runFast_arrayList_add {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 listAddr arrAddr : Nat} {elems : Array JvmVal} {v : JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr = some (.objArray "java/lang/Object" elems))
    (hcompat : v.isRef = true := by rfl) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc0, v :: .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 1 :: stk, locs, jh.set arrAddr (.objArray "java/lang/Object" (elems.push v)), hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  simp [Jvm.stepInvokeInterfaceGeneric, hlist, harr, Jvm.isArrayElemCompat]
  cases v <;> simp [Jvm.JvmVal.isRef] at hcompat ⊢

theorem runFast_collections_last {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 listAddr arrAddr : Nat} {arrCls : String} {elems : Array JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr = some (.objArray arrCls elems))
    (hpos : 0 < elems.size) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/collections/CollectionsKt" "last" "(Ljava/util/List;)Ljava/lang/Object;" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, elems[elems.size - 1] :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  simp [Jvm.stepInvokeStaticGeneric, mkTimeHooks, normalizeTimeClass, Jvm.extractListArray?,
    hlist, harr, hpos]

theorem runFast_collectionSizeOrDefault {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 listAddr arrAddr : Nat} {arrCls : String} {elems : Array JvmVal}
    {defVal : UInt32} {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr = some (.objArray arrCls elems)) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I" :: rest)
        ⟨pc0, .i32 defVal :: .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofNat elems.size) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_invokestatic_step _ ?_
  simp [Jvm.stepInvokeStaticGeneric, Jvm.extractListArray?,
    hlist, harr]

theorem runFast_arrayList_init {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 : Nat} {cap : UInt32}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hnonneg : cap.toBitVec.slt 0#32 = false) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokespecial "java/util/ArrayList" "<init>" "(I)V" :: rest)
        ⟨pc0, .i32 cap :: .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs,
          ((jh.alloc (.objArray "java/lang/Object" #[])).2.alloc
            (.instance "java/util/ArrayList" [("arr", .heapRef jh.objects.size)])).2,
          hp⟩ := by
  refine Jvm.runJvmResFast_invokespecial_step _ ?_
  simp only [Jvm.stepInvokeSpecialGeneric, Jvm.JvmVal.asI32?, hnonneg, Bool.false_eq_true, ↓reduceIte,
    Jvm.JvmHeap.alloc, Array.size_push]

theorem runFast_iterable_iterator {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc pc0 listAddr arrAddr : Nat} {arrCls : String} {elems : Array JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr = some (.objArray arrCls elems)) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;" :: rest)
        ⟨pc0, .heapRef listAddr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stk, locs,
          (jh.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])).2,
          hp⟩ := by
  refine Jvm.runJvmResFast_invokeinterface_step _ ?_
  simp [Jvm.stepInvokeInterfaceGeneric, Jvm.extractListArray?, hlist, harr, Jvm.JvmHeap.alloc]

theorem runFast_newClass {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {cls : String}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hne : (cls == "java/lang/StringBuilder") = false := by decide) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.newClass cls :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases d <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl

theorem runFast_astore {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 idx : Nat} {v : JvmVal}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) (f + 1) prog pc (.astore idx :: rest)
        ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg d subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) (.astore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := by
    cases d <;> rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg d subFuel) rfl (by simp) hs rfl

theorem ui32_ofNat_nonneg_of_lt {n : Nat} (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toBitVec.slt 0#32 = false :=
  Jvm.ui32_slt_zero_of_lt n hlt

theorem runJvmRes_step_nonbranch_eq {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f : Nat} {prog : List JvmInstr} {instr : JvmInstr} {st st' : JvmState}
    (hget : prog[st.pc]? = some instr) (hnbr : Jvm.isBranchInstr instr = false)
    (hstep : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel) instr st = .inl (some st')) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (f + 1) prog st =
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) f prog st' := by
  rw [Jvm.runJvmRes_nonbranch _ f prog st instr hget hnbr, hstep]

theorem runJvmRes_checkNotNull {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc : Nat} {prog : List JvmInstr} {param : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V"))
    (hnn : v.isNull = false) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (f + 1) prog
        ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) f prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg d subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
    cases d <;> dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric] <;> simp [hnn]
  exact runJvmRes_step_nonbranch_eq hget rfl hs

/-! ### 1–7: Core Period Arithmetic & Duration Equivalence Theorems -/

theorem getTotalNanoseconds_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 40 ≤ fuel)
    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_getTotalNanoseconds_prog
        (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (totalNanosecondsModel p).toUInt64, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 40) PeriodUntilKt_getTotalNanoseconds_prog 0
          PeriodUntilKt_getTotalNanoseconds_prog (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (totalNanosecondsModel p).toUInt64,
          ⟨30, [.i64 (totalNanosecondsModel p).toUInt64],
            setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_getTotalNanoseconds_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_int]
    rw [runFast_duration_inWholeNs]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_int]
    rw [runFast_duration_inWholeNs]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_int]
    rw [runFast_duration_inWholeNs]
    time_step_blk
    rw [runFast_lreturn]
    have heq :
        ((UInt64.ofBitVec (p.nanoseconds.toUInt32.toBitVec.signExtend 64) +
          (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds.toUInt64) +
          (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds.toUInt64) +
          (Duration.ofIntUnit p.hours .hours).inWholeNanoseconds.toUInt64 =
        (totalNanosecondsModel p).toUInt64 := by
      have hns : UInt64.ofBitVec (p.nanoseconds.toUInt32.toBitVec.signExtend 64) =
          (Int64.ofInt p.nanoseconds.toInt).toUInt64 := int32_signExtend_i64 p.nanoseconds
      rw [hns]
      rfl
    rw [heq]
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem dateComponentInWholeUnits_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (p : DateTimePeriodModel) (u : DateBasedUnit) (q : Int32)
    (hq : dateComponentInWholeUnitsModel p u = some q)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_dateComponentInWholeUnits_prog
        (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.dateBased u)))] hp jh) =
        some (.i32 q.toUInt32, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  apply runFast_exists0 rfl
  cases u with
  | dayBased daysUnit =>
    have hnz : daysUnit ≠ 0 := by
      intro h0; subst h0; simp [dateComponentInWholeUnitsModel] at hq
    have hq_eq : q = jvmI32Div p.days daysUnit := by
      have h0 : (daysUnit == 0) = false := beq_false_of_ne hnz
      simp [dateComponentInWholeUnitsModel, h0] at hq
      exact hq.symm
    have hrun :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 30)
            PeriodUntilKt_dateComponentInWholeUnits_prog 0 PeriodUntilKt_dateComponentInWholeUnits_prog
            (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.dateBased (.dayBased daysUnit))))]
              hp jh) =
          some (.i32 q.toUInt32,
            ⟨32, [.i32 q.toUInt32],
              setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.period p)))
                1 (.ext (.timeUnit (.dateBased (.dayBased daysUnit)))))
                2 (.ext (.timeUnit (.dateBased (.dayBased daysUnit)))),
              jh, hp⟩) := by
      simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_dateComponentInWholeUnits_prog]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_instanceof_ext, checkInst_day_day]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      time_step_blk
      rw [runFast_checkcast_ext (by rfl)]
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      rw [runFast_idiv hnz]
      rw [runFast_goto]
      (conv => lhs; tactic => time_norm_run_args)
      rw [runFast_ireturn]
      rw [hq_eq]
    exact ⟨_, hrun, rfl, rfl⟩
  | monthBased monthsUnit =>
    have hnz : monthsUnit ≠ 0 := by
      intro h0; subst h0; simp [dateComponentInWholeUnitsModel] at hq
    have hq_eq : q = jvmI32Div p.months monthsUnit := by
      have h0 : (monthsUnit == 0) = false := beq_false_of_ne hnz
      simp [dateComponentInWholeUnitsModel, h0] at hq
      exact hq.symm
    have hrun :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 30)
            PeriodUntilKt_dateComponentInWholeUnits_prog 0 PeriodUntilKt_dateComponentInWholeUnits_prog
            (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.dateBased (.monthBased monthsUnit))))]
              hp jh) =
          some (.i32 q.toUInt32,
            ⟨32, [.i32 q.toUInt32],
              setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.period p)))
                1 (.ext (.timeUnit (.dateBased (.monthBased monthsUnit)))))
                2 (.ext (.timeUnit (.dateBased (.monthBased monthsUnit)))),
              jh, hp⟩) := by
      simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_dateComponentInWholeUnits_prog]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_instanceof_ext, checkInst_day_month]
      rw [runFast_ifeq_zero]
      time_step_blk
      rw [runFast_instanceof_ext, checkInst_month_month]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      time_step_blk
      rw [runFast_checkcast_ext (by rfl)]
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      rw [runFast_idiv hnz]
      rw [runFast_goto]
      (conv => lhs; tactic => time_norm_run_args)
      rw [runFast_ireturn]
      rw [hq_eq]
    exact ⟨_, hrun, rfl, rfl⟩

theorem runJvmRes_ifeq_zero {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc target : Nat} {prog : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some (.ifeq target)) :
    Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog
        ⟨pc, .i32 0 :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog ⟨target, stk, locs, jh, hp⟩ := by
  dsimp only [Jvm.runJvmRes]
  rw [hget]
  rfl

theorem runJvmRes_ifeq_nonzero {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc target : Nat} {prog : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some (.ifeq target)) (hnz : v ≠ 0) :
    Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog
        ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog ⟨pc + 1, stk, locs, jh, hp⟩ := by
  dsimp only [Jvm.runJvmRes]
  rw [hget]
  have hb : (v == 0) = false := beq_false_of_ne hnz
  simp [mkTimeHooks, Jvm.JvmVal.asI32?, hb]

theorem runJvmRes_instanceof_ext {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc : Nat} {prog : List JvmInstr} {cls : String} {e : TimeExt}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some (.instanceof cls)) :
    Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog
        ⟨pc, .ext e :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog
        ⟨pc + 1, .i32 (if checkTimeInstanceOf cls (.ext e) then 1 else 0) :: stk, locs, jh, hp⟩ :=
  runJvmRes_step_nonbranch_eq hget rfl rfl

theorem runJvmRes_checkcast_ext {resolveProg : String → Option (List JvmInstr)}
    {d1 subFuel f pc : Nat} {prog : List JvmInstr} {cls : String} {e : TimeExt}
    (hget : prog[pc]? = some (.checkcast cls))
    (hcast : checkTimeCast cls (.ext e) = some (.ext e)) :
    Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog
        ⟨pc, .ext e :: stk, locs, jh, hp⟩ =
      Jvm.runJvmRes (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog
        ⟨pc + 1, .ext e :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) (.checkcast cls)
      ⟨pc, .ext e :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .ext e :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, mkTimeHooks]
    rw [hcast]
  exact runJvmRes_step_nonbranch_eq hget rfl hs

theorem runJvmRes_idiv_zero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc : Nat} {prog : List JvmInstr} {a : Int32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some .idiv) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (f + 1) prog
        ⟨pc, .i32 0 :: .i32 a.toUInt32 :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmRes_nonbranch _ f prog _ .idiv hget rfl]
  cases d <;> rfl

theorem runJvmRes_ldiv_zero {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc : Nat} {prog : List JvmInstr} {a : Int64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hget : prog[pc]? = some .ldiv) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (f + 1) prog
        ⟨pc, .i64 0 :: .i64 a.toUInt64 :: stk, locs, jh, hp⟩ = none := by
  rw [Jvm.runJvmRes_nonbranch _ f prog _ .ldiv hget rfl]
  cases d <;> rfl

theorem dateComponentInWholeUnits_divZero_traps (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (p : DateTimePeriodModel) (u : DateBasedUnit)
    (htrap : dateComponentInWholeUnitsModel p u = none)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_dateComponentInWholeUnits_prog
      (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.dateBased u)))] hp jh) = none := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  cases u with
  | dayBased daysUnit =>
    have hz : daysUnit = 0 := by
      by_cases h0 : daysUnit = 0
      · exact h0
      · have hne : (daysUnit == 0) = false := beq_false_of_ne h0
        simp [dateComponentInWholeUnitsModel, hne] at htrap
    subst hz
    rfl
  | monthBased monthsUnit =>
    have hz : monthsUnit = 0 := by
      by_cases h0 : monthsUnit = 0
      · exact h0
      · have hne : (monthsUnit == 0) = false := beq_false_of_ne h0
        simp [dateComponentInWholeUnitsModel, hne] at htrap
    subst hz
    rfl

theorem lookup_getTotalNanoseconds :
    timeProgLookup "PeriodUntilKt.getTotalNanoseconds:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getTotalNanoseconds_prog := by
  simp only [timeProgLookup, ↓reduceIte]

theorem runFast_call_getTotalNanoseconds {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hsf : 40 ≤ subFuel) (hd1 : 1 ≤ d1)
    {prog rest : List JvmInstr} {p : DateTimePeriodModel}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hc : HasTimeStaticsClean jh) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getTotalNanoseconds"
          "(Lkotlinx/datetime/DateTimePeriod;)J" :: rest)
        ⟨pc0, .ext (.period p) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (totalNanosecondsModel p).toUInt64 :: stk, locs, jh, hp⟩ := by
  have hprog : resolveProg "PeriodUntilKt.getTotalNanoseconds:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getTotalNanoseconds_prog := hext _ _ lookup_getTotalNanoseconds
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    getTotalNanoseconds_equiv resolveProg d1 subFuel subFuel hd1 hsf p hp jh hc
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getTotalNanoseconds" "(Lkotlinx/datetime/DateTimePeriod;)J")
      ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (totalNanosecondsModel p).toUInt64 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩)
      (method := "getTotalNanoseconds") (desc := "(Lkotlinx/datetime/DateTimePeriod;)J")
      (tags := ['L']) (args := [.ext (.period p)]) (stkRest := stk)
      (res := .i64 (totalNanosecondsModel p).toUInt64) (endSt := endSt)
      tags_periodArg rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem timeComponentInWholeUnits_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 40 ≤ subFuel) (hf : 20 ≤ fuel)
    (p : DateTimePeriodModel) (u : TimeBasedUnit) (q : Int64)
    (hq : timeComponentInWholeUnitsModel p u = some q)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_timeComponentInWholeUnits_prog
        (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.timeBased u)))] hp jh) =
        some (.i64 q.toUInt64, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 1 ≤ d1 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hnz : u.nanoseconds ≠ 0 := by
    intro h0; rw [timeComponentInWholeUnitsModel, h0] at hq; contradiction
  have hq_eq : q = jvmI64Div (totalNanosecondsModel p) u.nanoseconds := by
    have h0 : (u.nanoseconds == 0) = false := beq_false_of_ne hnz
    simp [timeComponentInWholeUnitsModel, h0] at hq
    exact hq.symm
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 20)
          PeriodUntilKt_timeComponentInWholeUnits_prog 0 PeriodUntilKt_timeComponentInWholeUnits_prog
          (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.timeBased u)))] hp jh) =
        some (.i64 q.toUInt64,
          ⟨11, [.i64 q.toUInt64],
            setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.period p))) 1 (.ext (.timeUnit (.timeBased u))),
            jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_timeComponentInWholeUnits_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_call_getTotalNanoseconds hext hsf hd1 hc]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    rw [runFast_ldiv hnz]
    rw [runFast_lreturn]
    rw [hq_eq]
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem timeComponentInWholeUnits_divZero_traps (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 40 ≤ subFuel) (hf : 20 ≤ fuel)
    (p : DateTimePeriodModel) (u : TimeBasedUnit)
    (htrap : timeComponentInWholeUnitsModel p u = none)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh) :
    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_timeComponentInWholeUnits_prog
      (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.timeBased u)))] hp jh) = none := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 1 ≤ d1 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨ns⟩ := u
  have hz : ns = 0 := by
    by_cases h0 : ns = 0
    · exact h0
    · have hne : (ns == 0) = false := beq_false_of_ne h0
      simp [timeComponentInWholeUnitsModel, hne] at htrap
  subst hz
  have hprog : resolveProg "PeriodUntilKt.getTotalNanoseconds:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getTotalNanoseconds_prog := hext _ _ lookup_getTotalNanoseconds
  obtain ⟨endSub, hsub, -, -⟩ :=
    getTotalNanoseconds_equiv resolveProg d1 subFuel subFuel hd1 hsf p hp jh hc
  simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
  rw [runJvmRes_step_nonbranch_eq (instr := .aload 0) rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .ldcStr "<this>") rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
    "(Ljava/lang/Object;Ljava/lang/String;)V") rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .aload 1) rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .ldcStr "unit") rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
    "(Ljava/lang/Object;Ljava/lang/String;)V") rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq (instr := .aload 0) rfl rfl rfl]
  rw [runJvmRes_step_nonbranch_eq
    (instr := .invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getTotalNanoseconds" "(Lkotlinx/datetime/DateTimePeriod;)J")
    rfl rfl (by
      dsimp only [Jvm.stepInstr]
      exact stepPeriodUntilKtStatic (tags := ['L']) (args := [.ext (.period p)]) (stkRest := [])
        tags_periodArg rfl (by rfl) hprog hsub)]
  rfl

theorem getTimeComponentDuration_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 40 ≤ subFuel) (hf : 20 ≤ fuel)
    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_getTimeComponentDuration_prog
        (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (timeComponentDurationModel p).rawValue.toUInt64, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 1 ≤ d1 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 20)
          PeriodUntilKt_getTimeComponentDuration_prog 0 PeriodUntilKt_getTimeComponentDuration_prog
          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (timeComponentDurationModel p).rawValue.toUInt64,
          ⟨9, [.i64 (timeComponentDurationModel p).rawValue.toUInt64],
            setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_getTimeComponentDuration_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [runFast_call_getTotalNanoseconds hext hsf hd1 hc]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_long]
    rw [runFast_lreturn]
    rfl
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem getDateComponentApproximateDuration_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 40 ≤ fuel)
    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh)
    (hNotNaN : (Duration.ofDaysFloat? ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)).isSome = true)
    (hPlusOk : (Duration.plus? (Duration.ofIntUnit p.days .days)
      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).isSome = true) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_getDateComponentApproximateDuration_prog
        (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨durF, hdurF⟩ := Option.isSome_iff_exists.mp hNotNaN
  have hdurF_eq : Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422) = durF := by
    simp [Duration.ofDaysFloat, hdurF]
  have hSum : ∃ durS, Duration.plus? (Duration.ofIntUnit p.days .days) durF = some durS := by
    rw [← hdurF_eq]
    exact Option.isSome_iff_exists.mp hPlusOk
  obtain ⟨durS, hdurS⟩ := hSum
  have hdurS_eq : Duration.plus (Duration.ofIntUnit p.days .days)
      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)) = durS := by
    rw [hdurF_eq]
    simp [Duration.plus, hdurS]
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 40)
          PeriodUntilKt_getDateComponentApproximateDuration_prog 0 PeriodUntilKt_getDateComponentApproximateDuration_prog
          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64,
          ⟨30, [.i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64],
            setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_getDateComponentApproximateDuration_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_int]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    have hc12 : Float.ofBits 4622945017495814144 = 12.0 := rfl
    have hc365 : Float.ofBits 4645133024925282678 = 365.2422 := rfl
    have hm_f : Jvm.i32ToFloat p.months.toUInt32 = p.months.toFloat := int32_toFloat_eq_i32ToFloat p.months
    have hy_f : Jvm.i32ToFloat p.years.toUInt32 = p.years.toFloat := int32_toFloat_eq_i32ToFloat p.years
    rw [hc12, hc365, hm_f, hy_f]
    rw [runFast_toDuration_daysFloat hdurF]
    rw [runFast_duration_plus hdurS]
    rw [runFast_duration_inWholeNs]
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    rw [runFast_toDuration_long]
    rw [runFast_lreturn]
    dsimp only [dateComponentApproximateDurationModel]
    rw [hdurS_eq]
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem lookup_getTimeComponentDuration :
    timeProgLookup "PeriodUntilKt.getTimeComponentDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getTimeComponentDuration_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem runFast_call_getTimeComponentDuration {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 2 ≤ d1) (hsf : 40 ≤ subFuel)
    {prog rest : List JvmInstr} {p : DateTimePeriodModel}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hc : HasTimeStaticsClean jh) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getTimeComponentDuration"
          "(Lkotlinx/datetime/DateTimePeriod;)J" :: rest)
        ⟨pc0, .ext (.period p) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (timeComponentDurationModel p).rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hprog : resolveProg "PeriodUntilKt.getTimeComponentDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getTimeComponentDuration_prog := hext _ _ lookup_getTimeComponentDuration
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    getTimeComponentDuration_equiv resolveProg hext d1 subFuel subFuel hd1 hsf (by omega) p hp jh hc
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getTimeComponentDuration" "(Lkotlinx/datetime/DateTimePeriod;)J")
      ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (timeComponentDurationModel p).rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩)
      (method := "getTimeComponentDuration") (desc := "(Lkotlinx/datetime/DateTimePeriod;)J")
      (tags := ['L']) (args := [.ext (.period p)]) (stkRest := stk)
      (res := .i64 (timeComponentDurationModel p).rawValue.toUInt64) (endSt := endSt)
      tags_periodArg rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem lookup_getDateComponentApproximateDuration :
    timeProgLookup "PeriodUntilKt.getDateComponentApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getDateComponentApproximateDuration_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem runFast_call_getDateComponentApproximateDuration
    {resolveProg : String → Option (List JvmInstr)} (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 1 ≤ d1) (hsf : 40 ≤ subFuel)
    {prog rest : List JvmInstr} {p : DateTimePeriodModel}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hc : HasTimeStaticsClean jh)
    (hNotNaN : (Duration.ofDaysFloat? ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)).isSome = true)
    (hPlusOk : (Duration.plus? (Duration.ofIntUnit p.days .days)
      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).isSome = true) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getDateComponentApproximateDuration"
          "(Lkotlinx/datetime/DateTimePeriod;)J" :: rest)
        ⟨pc0, .ext (.period p) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hprog : resolveProg
      "PeriodUntilKt.getDateComponentApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getDateComponentApproximateDuration_prog := hext _ _ lookup_getDateComponentApproximateDuration
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    getDateComponentApproximateDuration_equiv resolveProg d1 subFuel subFuel hd1 hsf p hp jh hc hNotNaN hPlusOk
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "getDateComponentApproximateDuration"
        "(Lkotlinx/datetime/DateTimePeriod;)J")
      ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.period p) :: stk, locs, jh, hp⟩)
      (method := "getDateComponentApproximateDuration")
      (desc := "(Lkotlinx/datetime/DateTimePeriod;)J")
      (tags := ['L']) (args := [.ext (.period p)]) (stkRest := stk)
      (res := .i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64) (endSt := endSt)
      tags_periodArg rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem getApproximateDuration_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 40 ≤ subFuel) (hf : 20 ≤ fuel)
    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh)
    (hNotNaN : (Duration.ofDaysFloat? ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)).isSome = true)
    (hPlusOk : (Duration.plus? (Duration.ofIntUnit p.days .days)
      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).isSome = true)
    (hApproxOk : (Duration.plus? (timeComponentDurationModel p)
      (dateComponentApproximateDurationModel p)).isSome = true) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_getApproximateDuration_prog
        (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (approximateDurationModel p).rawValue.toUInt64, endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 2 ≤ d1 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨durA, hdurA⟩ := Option.isSome_iff_exists.mp hApproxOk
  have hdurA_eq : approximateDurationModel p = durA := by
    simp [approximateDurationModel, Duration.plus, hdurA]
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 20)
          PeriodUntilKt_getApproximateDuration_prog 0 PeriodUntilKt_getApproximateDuration_prog
          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.i64 (approximateDurationModel p).rawValue.toUInt64,
          ⟨8, [.i64 (approximateDurationModel p).rawValue.toUInt64],
            setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_getApproximateDuration_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_call_getTimeComponentDuration hext hd1 hsf hc]
    time_step_blk
    rw [runFast_call_getDateComponentApproximateDuration hext (by omega) hsf hc hNotNaN hPlusOk]
    rw [runFast_duration_plus hdurA]
    rw [runFast_lreturn]
    rw [hdurA_eq]
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem lookup_getApproximateDuration :
    timeProgLookup "PeriodUntilKt.getApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getApproximateDuration_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem getApproximateDurationInMinutes_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 4 ≤ d) (hsf : 40 ≤ subFuel) (hf : 25 ≤ fuel)
    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh)
    (hNotNaN : (Duration.ofDaysFloat? ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)).isSome = true)
    (hPlusOk : (Duration.plus? (Duration.ofIntUnit p.days .days)
      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).isSome = true)
    (hApproxOk : (Duration.plus? (timeComponentDurationModel p)
      (dateComponentApproximateDurationModel p)).isSome = true) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_getApproximateDurationInMinutes_prog
        (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.f64 (approximateDurationInMinutesModel p), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 3 ≤ d1 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hprog : resolveProg "PeriodUntilKt.getApproximateDuration:(Lkotlinx/datetime/DateTimePeriod;)J" =
      some PeriodUntilKt_getApproximateDuration_prog := hext _ _ lookup_getApproximateDuration
  obtain ⟨endSub, hsub, hjh, hhp⟩ :=
    getApproximateDuration_equiv resolveProg hext d1 subFuel subFuel hd1 hsf (by omega) p hp jh hc
      hNotNaN hPlusOk hApproxOk
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 25)
          PeriodUntilKt_getApproximateDurationInMinutes_prog 0 PeriodUntilKt_getApproximateDurationInMinutes_prog
          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
        some (.f64 (approximateDurationInMinutesModel p),
          ⟨15, [.f64 (approximateDurationInMinutesModel p)],
            setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_getApproximateDurationInMinutes_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokestatic_step _ (by
      have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
        (st := ⟨4, [.ext (.period p)], setLocal (fun _ => .i32 0) 0 (.ext (.period p)), jh, hp⟩)
        (method := "getApproximateDuration") (desc := "(Lkotlinx/datetime/DateTimePeriod;)J")
        (tags := ['L']) (args := [.ext (.period p)]) (stkRest := [])
        (res := .i64 (approximateDurationModel p).rawValue.toUInt64) (endSt := endSub)
        tags_periodArg rfl rfl hprog hsub
      rw [hs, hjh, hhp])]
    rw [runFast_duration_inWholeNs]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    time_step_blk
    rw [runFast_getstatic_clean (hc _ _) (by rfl)]
    have h1 : (1 : UInt32) = (1 : Int32).toUInt32 := rfl
    rw [h1, runFast_toDuration_int (iv := (1 : Int32)) (u := .minutes)]
    rw [runFast_duration_inWholeNs]
    time_step_blk
    rw [runFast_dreturn]
    rfl
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

/-! ### 8–9: `periodUntilWithUnit` (2 Overloads) Equivalence Theorems -/

theorem periodUntilWithUnit_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 50 ≤ fuel)
    (start other : Int64) (u : DateTimeUnit) (tz : String)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntilWithUnit_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
          (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz))] hp jh) =
        some (.ext (.period (periodUntilWithUnitModel (hp.untilTz start other u tz) u)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  cases u with
  | timeBased tb =>
    have heq : (tb.nanoseconds.toUInt64 * (hp.untilTz start other (.timeBased tb) tz).toUInt64).toInt64 =
        tb.nanoseconds * hp.untilTz start other (.timeBased tb) tz := rfl
    have hrun :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 50)
            PeriodUntilKt_periodUntilWithUnit_prog 0 PeriodUntilKt_periodUntilWithUnit_prog
            (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
              (2, .ext (.timeUnit (.timeBased tb))), (3, .ext (.timeZone tz))] hp jh) =
          some (.ext (.period (periodUntilWithUnitModel (hp.untilTz start other (.timeBased tb) tz) (.timeBased tb))),
            ⟨82, [.ext (.period (periodUntilWithUnitModel (hp.untilTz start other (.timeBased tb) tz) (.timeBased tb)))],
              setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
                0 (.ext (.instant start))) 1 (.ext (.instant other)))
                2 (.ext (.timeUnit (.timeBased tb)))) 3 (.ext (.timeZone tz)))
                4 (.i64 (hp.untilTz start other (.timeBased tb) tz).toUInt64))
                6 (.ext (.timeUnit (.timeBased tb))),
              jh, hp⟩) := by
      simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithUnit_prog]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_checkNotNull (by rfl)]
      time_step_blk
      rw [runFast_instant_untilTz]
      time_step_blk
      rw [runFast_instanceof_ext, checkInst_tb_tb]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [runFast_checkcast_ext (by rfl)]
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      time_step_blk
      rw [runFast_dateTimePeriodDefault]
      rw [runFast_goto]
      (conv => lhs; tactic => time_norm_run_args)
      rw [runFast_areturn]
      simp [applyDateTimePeriodDefault, periodUntilWithUnitModel, heq]
    exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩
  | dateBased du =>
    cases du with
    | dayBased daysUnit =>
      have hmul : ((UInt64.ofBitVec (daysUnit.toUInt32.toBitVec.signExtend 64) *
            (hp.untilTz start other (.dateBased (.dayBased daysUnit)) tz).toUInt64).toUInt32).toInt32 =
          Int32.ofInt (Int64.ofInt daysUnit.toInt *
            hp.untilTz start other (.dateBased (.dayBased daysUnit)) tz).toInt := by
        rw [int32_signExtend_i64 daysUnit]
        exact int64_truncate_i32 _
      have hrun :
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 50)
              PeriodUntilKt_periodUntilWithUnit_prog 0 PeriodUntilKt_periodUntilWithUnit_prog
              (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                (2, .ext (.timeUnit (.dateBased (.dayBased daysUnit)))), (3, .ext (.timeZone tz))] hp jh) =
            some (.ext (.period (periodUntilWithUnitModel
                (hp.untilTz start other (.dateBased (.dayBased daysUnit)) tz) (.dateBased (.dayBased daysUnit)))),
              ⟨82, [.ext (.period (periodUntilWithUnitModel
                  (hp.untilTz start other (.dateBased (.dayBased daysUnit)) tz) (.dateBased (.dayBased daysUnit))))],
                setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
                  0 (.ext (.instant start))) 1 (.ext (.instant other)))
                  2 (.ext (.timeUnit (.dateBased (.dayBased daysUnit))))) 3 (.ext (.timeZone tz)))
                  4 (.i64 (hp.untilTz start other (.dateBased (.dayBased daysUnit)) tz).toUInt64))
                  6 (.ext (.timeUnit (.dateBased (.dayBased daysUnit)))),
                jh, hp⟩) := by
        simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
        conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithUnit_prog]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_instant_untilTz]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_tb_db]
        rw [runFast_ifeq_zero]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_day_day]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [runFast_checkcast_ext (by rfl)]
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        time_step_blk
        rw [runFast_dateTimePeriodDefault]
        rw [runFast_goto]
        (conv => lhs; tactic => time_norm_run_args)
        rw [runFast_areturn]
        dsimp only [applyDateTimePeriodDefault, periodUntilWithUnitModel]
        rw [hmul]
        rfl
      exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩
    | monthBased monthsUnit =>
      have hmul : ((UInt64.ofBitVec (monthsUnit.toUInt32.toBitVec.signExtend 64) *
            (hp.untilTz start other (.dateBased (.monthBased monthsUnit)) tz).toUInt64).toUInt32).toInt32 =
          Int32.ofInt (Int64.ofInt monthsUnit.toInt *
            hp.untilTz start other (.dateBased (.monthBased monthsUnit)) tz).toInt := by
        rw [int32_signExtend_i64 monthsUnit]
        exact int64_truncate_i32 _
      have hrun :
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 50)
              PeriodUntilKt_periodUntilWithUnit_prog 0 PeriodUntilKt_periodUntilWithUnit_prog
              (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                (2, .ext (.timeUnit (.dateBased (.monthBased monthsUnit)))), (3, .ext (.timeZone tz))] hp jh) =
            some (.ext (.period (periodUntilWithUnitModel
                (hp.untilTz start other (.dateBased (.monthBased monthsUnit)) tz)
                (.dateBased (.monthBased monthsUnit)))),
              ⟨82, [.ext (.period (periodUntilWithUnitModel
                  (hp.untilTz start other (.dateBased (.monthBased monthsUnit)) tz)
                  (.dateBased (.monthBased monthsUnit))))],
                setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
                  0 (.ext (.instant start))) 1 (.ext (.instant other)))
                  2 (.ext (.timeUnit (.dateBased (.monthBased monthsUnit))))) 3 (.ext (.timeZone tz)))
                  4 (.i64 (hp.untilTz start other (.dateBased (.monthBased monthsUnit)) tz).toUInt64))
                  6 (.ext (.timeUnit (.dateBased (.monthBased monthsUnit)))),
                jh, hp⟩) := by
        simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
        conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithUnit_prog]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_checkNotNull (by rfl)]
        time_step_blk
        rw [runFast_instant_untilTz]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_tb_db]
        rw [runFast_ifeq_zero]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_day_month]
        rw [runFast_ifeq_zero]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_month_month]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [runFast_checkcast_ext (by rfl)]
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        time_step_blk
        rw [runFast_dateTimePeriodDefault]
        rw [runFast_goto]
        (conv => lhs; tactic => time_norm_run_args)
        rw [runFast_areturn]
        dsimp only [applyDateTimePeriodDefault, periodUntilWithUnitModel]
        rw [hmul]
        rfl
      exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

theorem periodUntilWithUnit_1_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 30 ≤ fuel)
    (start other : Int64) (tu : TimeBasedUnit)
    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) :
    ∃ endSt,
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntilWithUnit_1_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
          (2, .ext (.timeUnit (.timeBased tu)))] hp jh) =
        some (.ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu)), endSt) ∧
      endSt.jvmHeap = jh ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have heq : (tu.nanoseconds.toUInt64 * (hp.untilTime start other tu).toUInt64).toInt64 =
      tu.nanoseconds * hp.untilTime start other tu := rfl
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 30)
          PeriodUntilKt_periodUntilWithUnit_1_prog 0 PeriodUntilKt_periodUntilWithUnit_1_prog
          (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
            (2, .ext (.timeUnit (.timeBased tu)))] hp jh) =
        some (.ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu)),
          ⟨25, [.ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu))],
            setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.instant start)))
              1 (.ext (.instant other))) 2 (.ext (.timeUnit (.timeBased tu))),
            jh, hp⟩) := by
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithUnit_1_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
    time_step_blk
    rw [runFast_instant_untilTime]
    time_step_blk
    rw [runFast_dateTimePeriodDefault]
    rw [runFast_areturn]
    simp [applyDateTimePeriodDefault, periodUntilWithUnitTimeModel, heq]
  exact runFast_exists0 rfl ⟨_, hrun, rfl, rfl⟩

/-! ### 10–11: `periodUntilWithProgressiveUnits` (2 Overloads) Equivalence Theorems -/

def unitPairVal (u : DateTimeUnit) (p : DateTimePeriodModel) : JvmVal :=
  .pair (.ext (.timeUnit u)) (.ext (.period p))

def unitTimePairVal (u : TimeBasedUnit) (p : DateTimePeriodModel) : JvmVal :=
  .pair (.ext (.timeUnit (.timeBased u))) (.ext (.period p))

def unitListNonZero (u : DateTimeUnit) : Bool :=
  match u with
  | .timeBased tb => tb.nanoseconds != 0
  | .dateBased (.dayBased d) => d != 0
  | .dateBased (.monthBased m) => m != 0

def periodNoAbsMin (p : DateTimePeriodModel) (u : DateTimeUnit) : Prop :=
  match u with
  | .timeBased tu =>
    ∃ q, timeComponentInWholeUnitsModel p tu = some q ∧ q ≠ (-9223372036854775808 : Int64)
  | .dateBased du =>
    ∃ q, dateComponentInWholeUnitsModel p du = some q ∧ q ≠ (-2147483648 : Int32)

theorem i64_abs_cmp_pos (v : Int64) (hNotMin : v ≠ (-9223372036854775808 : Int64)) :
    (if (if v.toUInt64.toBitVec.slt 0#64 then -v.toUInt64 else v.toUInt64) == 0 then (0 : UInt32)
      else if (if v.toUInt64.toBitVec.slt 0#64 then -v.toUInt64 else v.toUInt64).toBitVec.slt 0#64
        then 4294967295 else 1).toBitVec.sle 0#32 =
    !(v != 0) := by
  by_cases hv : v = 0
  · subst hv; decide
  · have hnu : v.toUInt64 ≠ 0 :=
      fun h => hv (Int64.toBitVec_inj.mp (by simpa using congrArg UInt64.toBitVec h))
    have hneq : (v != 0) = true := bne_iff_ne.mpr hv
    rw [hneq]
    by_cases hs : v.toUInt64.toBitVec.slt 0#64 = true
    · have hneqm : v.toUInt64.toBitVec.toInt ≠ -(2 ^ 63) := by
        intro h; apply hNotMin; apply Int64.toBitVec_inj.mp; exact BitVec.eq_of_toInt_eq h
      have hlo := v.toUInt64.toBitVec.le_toInt
      have hlt : v.toUInt64.toBitVec.toInt < 0 := by simpa [BitVec.slt] using hs
      have hpos : 0 < (-v.toUInt64.toBitVec).toInt := by
        rw [BitVec.toInt_neg, Int.bmod_eq_of_le_mul_two] <;> omega
      have hne0 : ((-v.toUInt64) == 0) = false := by
        apply beq_false_of_ne; intro h
        have h0 : (-v.toUInt64.toBitVec).toInt = 0 := by simpa using congrArg (fun z => z.toBitVec.toInt) h
        omega
      have hnslt : ((-v.toUInt64).toBitVec.slt 0#64) = false := by
        change decide ((-v.toUInt64.toBitVec).toInt < 0) = false; exact decide_eq_false (by omega)
      simp only [hs, ↓reduceIte, hne0, Bool.false_eq_true, hnslt, Bool.not_true]; decide
    · have hne0 : (v.toUInt64 == 0) = false := beq_false_of_ne hnu
      simp only [hs, Bool.false_eq_true, ↓reduceIte, hne0, Bool.not_true]; decide

theorem i32_abs_le_zero (v : Int32) (hNotMin : v ≠ (-2147483648 : Int32)) :
    (if v.toUInt32.toBitVec.slt 0#32 then -v.toUInt32 else v.toUInt32).toBitVec.sle 0#32 =
    !(v != 0) := by
  by_cases hv : v = 0
  · subst hv; decide
  · have hnu : v.toUInt32 ≠ 0 :=
      fun h => hv (Int32.toBitVec_inj.mp (by simpa using congrArg UInt32.toBitVec h))
    have hneq : (v != 0) = true := bne_iff_ne.mpr hv
    rw [hneq]
    by_cases hs : v.toUInt32.toBitVec.slt 0#32 = true
    · have hneqm : v.toUInt32.toBitVec.toInt ≠ -(2 ^ 31) := by
        intro h; apply hNotMin; apply Int32.toBitVec_inj.mp; exact BitVec.eq_of_toInt_eq h
      have hlo := v.toUInt32.toBitVec.le_toInt
      have hlt : v.toUInt32.toBitVec.toInt < 0 := by simpa [BitVec.slt] using hs
      have hpos : 0 < (-v.toUInt32.toBitVec).toInt := by
        rw [BitVec.toInt_neg, Int.bmod_eq_of_le_mul_two] <;> omega
      simp only [hs, ↓reduceIte, Bool.not_true]
      change decide ((-v.toUInt32.toBitVec).toInt ≤ 0) = false
      exact decide_eq_false (by omega)
    · have hns : ¬ (v.toUInt32.toBitVec.toInt < 0) := by
        intro h; exact hs (by simpa [BitVec.slt] using h)
      have hne0 : v.toUInt32.toBitVec.toInt ≠ 0 := by
        intro h; apply hnu; apply UInt32.toBitVec_inj.mp; exact BitVec.eq_of_toInt_eq h
      simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      change decide (v.toUInt32.toBitVec.toInt ≤ 0) = false
      exact decide_eq_false (by omega)

theorem lookup_periodUntilWithUnit :
    timeProgLookup
      "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;" =
      some PeriodUntilKt_periodUntilWithUnit_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem lookup_periodUntilWithUnit_1 :
    timeProgLookup
      "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;" =
      some PeriodUntilKt_periodUntilWithUnit_1_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem lookup_timeComponentInWholeUnits :
    timeProgLookup
      "PeriodUntilKt.timeComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" =
      some PeriodUntilKt_timeComponentInWholeUnits_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem lookup_dateComponentInWholeUnits :
    timeProgLookup
      "PeriodUntilKt.dateComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I" =
      some PeriodUntilKt_dateComponentInWholeUnits_prog := by
  simp only [timeProgLookup, String.reduceEq, ↓reduceIte]

theorem runFast_call_periodUntilWithUnit {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 1 ≤ d1) (hsf : 50 ≤ subFuel)
    {prog rest : List JvmInstr} {start other : Int64} {u : DateTimeUnit} {tz : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithUnit"
          "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;" :: rest)
        ⟨pc0, .ext (.timeZone tz) :: .ext (.timeUnit u) :: .ext (.instant other) ::
          .ext (.instant start) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.period (periodUntilWithUnitModel (hp.untilTz start other u tz) u)) :: stk,
          locs, jh, hp⟩ := by
  have hprog : resolveProg
      "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;" =
      some PeriodUntilKt_periodUntilWithUnit_prog := hext _ _ lookup_periodUntilWithUnit
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    periodUntilWithUnit_equiv resolveProg d1 subFuel subFuel hd1 (by omega) start other u tz hp jh
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithUnit"
        "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;")
      ⟨pc, .ext (.timeZone tz) :: .ext (.timeUnit u) :: .ext (.instant other) ::
        .ext (.instant start) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .ext (.period (periodUntilWithUnitModel (hp.untilTz start other u tz) u)) :: stk,
        locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.timeZone tz) :: .ext (.timeUnit u) :: .ext (.instant other) ::
        .ext (.instant start) :: stk, locs, jh, hp⟩)
      (method := "periodUntilWithUnit")
      (desc := "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)Lkotlinx/datetime/DateTimePeriod;")
      (tags := ['L', 'L', 'L', 'L'])
      (args := [.ext (.instant start), .ext (.instant other), .ext (.timeUnit u), .ext (.timeZone tz)])
      (stkRest := stk)
      (res := .ext (.period (periodUntilWithUnitModel (hp.untilTz start other u tz) u))) (endSt := endSt)
      tags_periodUntilWithUnit rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem runFast_call_periodUntilWithUnit_1 {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 1 ≤ d1) (hsf : 40 ≤ subFuel)
    {prog rest : List JvmInstr} {start other : Int64} {tu : TimeBasedUnit}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithUnit"
          "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;" :: rest)
        ⟨pc0, .ext (.timeUnit (.timeBased tu)) :: .ext (.instant other) ::
          .ext (.instant start) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu)) :: stk,
          locs, jh, hp⟩ := by
  have hprog : resolveProg
      "PeriodUntilKt.periodUntilWithUnit:(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;" =
      some PeriodUntilKt_periodUntilWithUnit_1_prog := hext _ _ lookup_periodUntilWithUnit_1
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    periodUntilWithUnit_1_equiv resolveProg d1 subFuel subFuel hd1 (by omega) start other tu hp jh
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "periodUntilWithUnit"
        "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;")
      ⟨pc, .ext (.timeUnit (.timeBased tu)) :: .ext (.instant other) ::
        .ext (.instant start) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1,
        .ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu)) :: stk,
        locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.timeUnit (.timeBased tu)) :: .ext (.instant other) ::
        .ext (.instant start) :: stk, locs, jh, hp⟩)
      (method := "periodUntilWithUnit")
      (desc := "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)Lkotlinx/datetime/DateTimePeriod;")
      (tags := ['L', 'L', 'L'])
      (args := [.ext (.instant start), .ext (.instant other), .ext (.timeUnit (.timeBased tu))])
      (stkRest := stk)
      (res := .ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu))) (endSt := endSt)
      tags_periodUntilWithUnit_1 rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem runFast_call_timeComponentInWholeUnits {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 2 ≤ d1) (hsf : 40 ≤ subFuel)
    {prog rest : List JvmInstr} {p : DateTimePeriodModel} {tu : TimeBasedUnit} {q : Int64}
    (hq : timeComponentInWholeUnitsModel p tu = some q)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap}
    (hc : HasTimeStaticsClean jh) :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "timeComponentInWholeUnits"
          "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" :: rest)
        ⟨pc0, .ext (.timeUnit (.timeBased tu)) :: .ext (.period p) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i64 q.toUInt64 :: stk, locs, jh, hp⟩ := by
  have hprog : resolveProg
      "PeriodUntilKt.timeComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J" =
      some PeriodUntilKt_timeComponentInWholeUnits_prog := hext _ _ lookup_timeComponentInWholeUnits
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    timeComponentInWholeUnits_equiv resolveProg hext d1 subFuel subFuel hd1 hsf (by omega) p tu q hq hp jh hc
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "timeComponentInWholeUnits"
        "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J")
      ⟨pc, .ext (.timeUnit (.timeBased tu)) :: .ext (.period p) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 q.toUInt64 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.timeUnit (.timeBased tu)) :: .ext (.period p) :: stk, locs, jh, hp⟩)
      (method := "timeComponentInWholeUnits")
      (desc := "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J")
      (tags := ['L', 'L'])
      (args := [.ext (.period p), .ext (.timeUnit (.timeBased tu))]) (stkRest := stk)
      (res := .i64 q.toUInt64) (endSt := endSt) tags_timeComponentInWholeUnits rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem runFast_call_dateComponentInWholeUnits {resolveProg : String → Option (List JvmInstr)}
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel f pc pc0 : Nat} (hd1 : 1 ≤ d1) (hsf : 40 ≤ subFuel)
    {prog rest : List JvmInstr} {p : DateTimePeriodModel} {du : DateBasedUnit} {q : Int32}
    (hq : dateComponentInWholeUnitsModel p du = some q)
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap TimeExt} {hp : TimeHeap} :
    Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (f + 1) prog pc
        (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "dateComponentInWholeUnits"
          "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I" :: rest)
        ⟨pc0, .ext (.timeUnit (.dateBased du)) :: .ext (.period p) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 q.toUInt32 :: stk, locs, jh, hp⟩ := by
  have hprog : resolveProg
      "PeriodUntilKt.dateComponentInWholeUnits:(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I" =
      some PeriodUntilKt_dateComponentInWholeUnits_prog := hext _ _ lookup_dateComponentInWholeUnits
  obtain ⟨endSt, hrun, hjh, hhp⟩ :=
    dateComponentInWholeUnits_equiv resolveProg d1 subFuel subFuel hd1 (by omega) p du q hq hp jh
  have hstep : Jvm.stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel)
      (.invokestatic "com/alexvanyo/composelife/timeutil/PeriodUntilKt" "dateComponentInWholeUnits"
        "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I")
      ⟨pc, .ext (.timeUnit (.dateBased du)) :: .ext (.period p) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 q.toUInt32 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr]
    have hs := stepPeriodUntilKtStatic (resolveProg := resolveProg) (d1 := d1) (subFuel := subFuel)
      (st := ⟨pc, .ext (.timeUnit (.dateBased du)) :: .ext (.period p) :: stk, locs, jh, hp⟩)
      (method := "dateComponentInWholeUnits")
      (desc := "(Lkotlinx/datetime/DateTimePeriod;Lkotlinx/datetime/DateTimeUnit$DateBased;)I")
      (tags := ['L', 'L'])
      (args := [.ext (.period p), .ext (.timeUnit (.dateBased du))]) (stkRest := stk)
      (res := .i32 q.toUInt32) (endSt := endSt) tags_dateComponentInWholeUnits rfl rfl hprog hrun
    rw [hs, hjh, hhp]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkTimeHooks resolveProg (d1 + 1) subFuel) rfl (by simp) hstep rfl

theorem jvmHeap_get_set_same {Ext : Type} {jh : Jvm.JvmHeap Ext} {addr : Nat}
    {obj : Jvm.HeapObj Ext} (hlt : addr < jh.objects.size) :
    (jh.set addr obj).get? addr = some obj := by
  simp [Jvm.JvmHeap.set, hlt, Jvm.JvmHeap.get?]

theorem jvmHeap_get_set_ne {Ext : Type} {jh : Jvm.JvmHeap Ext} {a b : Nat}
    {obj : Jvm.HeapObj Ext} (hne : a ≠ b) :
    (jh.set a obj).get? b = jh.get? b := by
  dsimp only [Jvm.JvmHeap.set, Jvm.JvmHeap.get?]
  split
  · simp [hne]
  · rfl

theorem jvmHeap_set_size {Ext : Type} (jh : Jvm.JvmHeap Ext) (addr : Nat)
    (obj : Jvm.HeapObj Ext) :
    (jh.set addr obj).objects.size = jh.objects.size := by
  dsimp only [Jvm.JvmHeap.set]
  split <;> simp

theorem jvmHeap_getStatic_set {Ext : Type} (jh : Jvm.JvmHeap Ext) (addr : Nat)
    (obj : Jvm.HeapObj Ext) (cls fld : String) :
    (jh.set addr obj).getStatic? cls fld = jh.getStatic? cls fld := by
  dsimp only [Jvm.JvmHeap.set]
  split <;> rfl

theorem jvmHeap_staticsClean_set {jh : Jvm.JvmHeap TimeExt} (hc : HasTimeStaticsClean jh)
    (addr : Nat) (obj : Jvm.HeapObj TimeExt) :
    HasTimeStaticsClean (jh.set addr obj) :=
  fun cls fld => by rw [jvmHeap_getStatic_set]; exact hc cls fld

theorem jvmHeap_staticsClean_alloc {jh : Jvm.JvmHeap TimeExt} (hc : HasTimeStaticsClean jh)
    (obj : Jvm.HeapObj TimeExt) :
    HasTimeStaticsClean (jh.alloc obj).2 :=
  fun _ _ => hc _ _

theorem jvmHeap_get_alloc_lt {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext)
    {addr : Nat} (hlt : addr < jh.objects.size) :
    (jh.alloc obj).2.get? addr = jh.get? addr := by
  dsimp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
  rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]

theorem jvmHeap_get_alloc_self {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (jh.alloc obj).2.get? jh.objects.size = some obj := by
  dsimp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
  simp

theorem progressiveMapLoop_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel : Nat} (hd1 : 1 ≤ d1) (hsf : 50 ≤ subFuel)
    (start other : Int64) (units : List DateTimeUnit) (tz : String)
    (arrAddr newArrAddr newListAddr itAddr : Nat)
    (hp : TimeHeap) :
    ∀ rem : Nat, ∀ idx : Nat, ∀ acc : Array JvmVal, ∀ jh : Jvm.JvmHeap TimeExt,
      ∀ locs : Nat → JvmVal, ∀ k : Nat,
      idx + rem = units.length →
      jh.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) →
      jh.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]) →
      jh.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) →
      jh.get? newArrAddr = some (.objArray "java/lang/Object" acc) →
      locs 0 = .ext (.instant start) →
      locs 1 = .ext (.instant other) →
      locs 3 = .ext (.timeZone tz) →
      locs 8 = .heapRef newListAddr →
      locs 10 = .heapRef itAddr →
      itAddr ≠ newArrAddr → itAddr ≠ newListAddr → itAddr ≠ arrAddr →
      newArrAddr ≠ arrAddr → newArrAddr ≠ newListAddr →
      units.length < 2 ^ 31 →
      ∃ jhEnd locsEnd,
        (jhEnd.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) ∧
        jhEnd.get? newArrAddr = some (.objArray "java/lang/Object"
          (acc ++ ((units.drop idx).map fun u =>
            unitPairVal u (periodUntilWithUnitModel (hp.untilTz start other u tz) u)).toArray)) ∧
        (HasTimeStaticsClean jh → HasTimeStaticsClean jhEnd) ∧
        locsEnd 8 = .heapRef newListAddr ∧
        newArrAddr < jhEnd.objects.size ∧ newListAddr < jhEnd.objects.size ∧
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 3 + 25 * rem)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 33 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 33)
            ⟨33, [], locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) k
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 58 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 58)
            ⟨58, [], locsEnd, jhEnd, hp⟩) := by
  intro rem
  induction rem with
  | zero =>
    intro idx acc jh locs k hlen harr hit hlist hnewArr hl0 hl1 hl3 hl8 hl10
      hne1 hne2 hne3 hne4 hne5 hlen31
    have hidx_eq : idx = units.length := by omega
    subst hidx_eq
    have hnewArrLt : newArrAddr < jh.objects.size :=
      (Array.getElem?_eq_some_iff.mp hnewArr).1
    have hnewListLt : newListAddr < jh.objects.size :=
      (Array.getElem?_eq_some_iff.mp hlist).1
    refine ⟨jh, locs, hlist, ?_, fun hc => hc, hl8, hnewArrLt, hnewListLt, ?_⟩
    · simp [List.drop_length, hnewArr]
    · have h1 : (UInt32.ofNat units.length).toNat = units.length := by
        simp [Nat.mod_eq_of_lt (by omega : units.length < 2 ^ 32)]
      have hlt_false : ¬ (UInt32.ofNat units.length).toNat <
          (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray.size := by
        simp [h1]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
      time_step_blk
      rw [hl10]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hlt_false, ↓reduceIte]
      rw [runFast_ifeq_zero]
  | succ r ih =>
    intro idx acc jh locs k hlen harr hit hlist hnewArr hl0 hl1 hl3 hl8 hl10
      hne1 hne2 hne3 hne4 hne5 hlen31
    have hidx_lt : idx < units.length := by omega
    have hidx_toNat : (UInt32.ofNat idx).toNat = idx := by
      simp [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)]
    have hitLt : itAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hit).1
    have hnewArrLt : newArrAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hnewArr).1
    let u := units[idx]
    let p := periodUntilWithUnitModel (hp.untilTz start other u tz) u
    let pairV := unitPairVal u p
    let jh1 := jh.set itAddr
      (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx + 1))])
    let jh2 := jh1.set newArrAddr (.objArray "java/lang/Object" (acc.push pairV))
    have hidx_u32 : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
      rw [UInt32.ofNat_add]; rfl
    have harr1 : jh1.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne3]; exact harr
    have hlist1 : jh1.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne2]; exact hlist
    have hnewArr1 : jh1.get? newArrAddr = some (.objArray "java/lang/Object" acc) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne1]; exact hnewArr
    have harr2 : jh2.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) := by
      dsimp only [jh2]; rw [jvmHeap_get_set_ne hne4]; exact harr1
    have hlist2 : jh2.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
      dsimp only [jh2]; rw [jvmHeap_get_set_ne hne5]; exact hlist1
    have hnewArr2 : jh2.get? newArrAddr = some (.objArray "java/lang/Object" (acc.push pairV)) := by
      dsimp only [jh2]; exact jvmHeap_get_set_same (by rw [jvmHeap_set_size]; exact hnewArrLt)
    have hit2 : jh2.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))]) := by
      dsimp only [jh2, jh1]
      rw [jvmHeap_get_set_ne (Ne.symm hne1), jvmHeap_get_set_same hitLt, hidx_u32]
    let locs1 := setLocal (setLocal (setLocal (setLocal locs
      11 (.ext (.timeUnit u))) 12 (.ext (.timeUnit u))) 15 (.heapRef newListAddr)) 13 (.i32 0)
    have hlocs_step :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) ((k + 3 + 25 * r) + 25)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 33 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 33)
            ⟨33, [], locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 3 + 25 * r)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 33 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 33)
            ⟨33, [], locs1, jh2, hp⟩ := by
      have hdrop_u : (units.map fun x => Jvm.JvmVal.ext (TimeExt.timeUnit x)).toArray[idx]'(by simp [hidx_lt]) =
          .ext (.timeUnit u) := by
        simp [u]
      have hsz_lt : (UInt32.ofNat idx).toNat <
          (units.map fun x => Jvm.JvmVal.ext (TimeExt.timeUnit x)).toArray.size := by
        simp [hidx_toNat, hidx_lt]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
      time_step_blk
      rw [hl10]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hsz_lt, ↓reduceIte]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [hl10]
      rw [runFast_iterator_next hit harr hsz_lt]
      simp only [hidx_toNat, hdrop_u]
      time_step_blk
      rw [hl8]
      time_step_blk
      rw [runFast_checkcast_ext (by rfl)]
      time_step_blk
      rw [hl0, hl1, hl3]
      rw [runFast_call_periodUntilWithUnit hext hd1 hsf]
      rw [runFast_tuples_to]
      time_step_blk
      rw [runFast_arrayList_add hlist1 hnewArr1]
      time_step_blk
      rw [runFast_goto]
      rfl
    have h0_1 : locs1 0 = .ext (.instant start) := by simp [locs1, setLocal, hl0]
    have h1_1 : locs1 1 = .ext (.instant other) := by simp [locs1, setLocal, hl1]
    have h3_1 : locs1 3 = .ext (.timeZone tz) := by simp [locs1, setLocal, hl3]
    have h8_1 : locs1 8 = .heapRef newListAddr := by simp [locs1, setLocal, hl8]
    have h10_1 : locs1 10 = .heapRef itAddr := by simp [locs1, setLocal, hl10]
    obtain ⟨jhEnd, locsEnd, h1, h2, h3, h4, h5, h6, hrun_ih⟩ :=
      ih (idx + 1) (acc.push pairV) jh2 locs1 k (by omega) harr2 hit2 hlist2 hnewArr2
        h0_1 h1_1 h3_1 h8_1 h10_1 hne1 hne2 hne3 hne4 hne5 hlen31
    refine ⟨jhEnd, locsEnd, h1, ?_, fun hc => h3 (jvmHeap_staticsClean_set (jvmHeap_staticsClean_set hc _ _) _ _),
      h4, h5, h6, ?_⟩
    · rw [h2, List.drop_eq_getElem_cons hidx_lt]
      simp [u, p, pairV]
      rw [List.drop_eq_getElem_cons (i := idx)
        (l := List.map (fun u => unitPairVal u (periodUntilWithUnitModel (hp.untilTz start other u tz) u)) units)
        (by simp [hidx_lt])]
      simp
    · rw [show k + 3 + 25 * (r + 1) = (k + 3 + 25 * r) + 25 from by omega]
      rw [hlocs_step, hrun_ih]

def isNonZeroUnitPair (pr : DateTimeUnit × DateTimePeriodModel) : Bool :=
  match pr.1 with
  | .timeBased tu =>
    match timeComponentInWholeUnitsModel pr.2 tu with
    | some v => v != 0
    | none => false
  | .dateBased du =>
    match dateComponentInWholeUnitsModel pr.2 du with
    | some v => v != 0
    | none => false

theorem isNonZeroUnitPair_eq_model (pairs : List (DateTimeUnit × DateTimePeriodModel))
    (hnePairs : pairs ≠ []) :
    (periodUntilWithProgressiveUnitsModel pairs) =
      some ((pairs.find? isNonZeroUnitPair).getD (pairs[pairs.length - 1]'
        (by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp))) := by
  change (match pairs.find? isNonZeroUnitPair with
    | some pair => some pair
    | none => pairs.getLast?) = _
  cases hf : pairs.find? isNonZeroUnitPair with
  | some pr => rfl
  | none =>
    have hpos : 0 < pairs.length := by
      cases pairs with
      | nil => exact absurd rfl hnePairs
      | cons _ _ => simp
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl

theorem progressiveFindLoop_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel : Nat} (hd1 : 2 ≤ d1) (hsf : 50 ≤ subFuel)
    (pairs : List (DateTimeUnit × DateTimePeriodModel))
    (hnePairs : pairs ≠ []) (hlen31 : pairs.length < 2 ^ 31)
    (hNotMin : ∀ pr ∈ pairs, periodNoAbsMin pr.2 pr.1)
    (arrAddr listAddr itAddr : Nat) (hp : TimeHeap) :
    ∀ rem : Nat, ∀ idx : Nat, ∀ jh : Jvm.JvmHeap TimeExt,
      ∀ locs : Nat → JvmVal, ∀ fuel : Nat,
      idx + rem = pairs.length →
      45 * rem + 20 ≤ fuel →
      HasTimeStaticsClean jh →
      jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) →
      jh.get? arrAddr =
        some (.objArray "java/lang/Object" (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray) →
      jh.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]) →
      locs 4 = .heapRef listAddr →
      locs 8 = .heapRef itAddr →
      itAddr ≠ arrAddr → itAddr ≠ listAddr →
      let resPair := ((pairs.drop idx).find? isNonZeroUnitPair).getD (pairs[pairs.length - 1]'
        (by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp))
      ∃ endSt,
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) fuel
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
            ⟨70, [], locs, jh, hp⟩ =
          some (unitPairVal resPair.1 resPair.2, endSt) ∧
        HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  intro rem
  induction rem with
  | zero =>
    intro idx jh locs fuel hlen hfuel hc hlist harr hit hl4 hl8 hne1 hne2
    have hidx_eq : idx = pairs.length := by omega
    subst hidx_eq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 15 ≤ fuel)
    have hpos : 0 < (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray.size := by
      cases pairs with
      | nil => exact absurd rfl hnePairs
      | cons _ _ => simp
    have hlast : (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray[
        (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray.size - 1] =
        unitPairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
          (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2 := by
      simp [unitPairVal]
    have h1 : (UInt32.ofNat pairs.length).toNat = pairs.length := by
      simp [Nat.mod_eq_of_lt (by omega : pairs.length < 2 ^ 32)]
    have hlt_false : ¬ (UInt32.ofNat pairs.length).toNat <
        (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray.size := by
      simp [h1]
    have hres :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 15)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
            ⟨70, [], locs, jh, hp⟩ =
          some (unitPairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
              (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2,
            ⟨135,
              [unitPairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
                (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2],
              locs, jh, hp⟩) := by
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
      time_step_blk
      rw [hl8]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hlt_false, ↓reduceIte]
      rw [runFast_ifeq_zero]
      time_step_blk
      rw [runFast_checkcast_null]
      time_step_blk
      rw [runFast_ifnonnull_fallthrough]
      time_step_blk
      rw [hl4]
      rw [runFast_collections_last hlist harr hpos]
      rw [hlast]
      dsimp only [unitPairVal]
      rw [runFast_checkcast_pair]
      rw [runFast_areturn]
    have hdrop : (pairs.drop pairs.length).find? isNonZeroUnitPair = none := by
      simp [List.drop_length]
    simp only [hdrop, Option.getD_none]
    exact ⟨_, hres, hc, rfl⟩
  | succ r ih =>
    intro idx jh locs fuel hlen hfuel hc hlist harr hit hl4 hl8 hne1 hne2
    have hidx_lt : idx < pairs.length := by omega
    have hidx_toNat : (UInt32.ofNat idx).toNat = idx := by
      simp [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)]
    have hitLt : itAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hit).1
    obtain ⟨⟨u, p⟩, hpr⟩ : ∃ pr, pairs[idx] = pr := ⟨_, rfl⟩
    let jh1 := jh.set itAddr
      (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx + 1))])
    have hidx_u32 : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
      rw [UInt32.ofNat_add]; rfl
    have hlist1 : jh1.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne2]; exact hlist
    have harr1 : jh1.get? arrAddr =
        some (.objArray "java/lang/Object" (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne1]; exact harr
    have hit1 : jh1.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_same hitLt, hidx_u32]
    have hsz_lt : (UInt32.ofNat idx).toNat <
        (pairs.map fun x => unitPairVal x.1 x.2).toArray.size := by
      simp [hidx_toNat, hidx_lt]
    have hdrop_pr : (pairs.map fun x => unitPairVal x.1 x.2).toArray[idx]'(by simp [hidx_lt]) =
        unitPairVal u p := by
      simp [hpr, unitPairVal]
    have hc1 : HasTimeStaticsClean jh1 := jvmHeap_staticsClean_set hc _ _
    have hnm : periodNoAbsMin p u := hNotMin (u, p) (hpr ▸ List.getElem_mem hidx_lt)
    have hhead : ∀ k,
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 23)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
            ⟨70, [], locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 1)
            PeriodUntilKt_periodUntilWithProgressiveUnits_prog 92 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 92)
            ⟨92, [.ext (.timeUnit u)],
              setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
                9 (unitPairVal u p)) 10 (unitPairVal u p)) 11 (.i32 0))
                12 (.ext (.timeUnit u))) 13 (.ext (.period p))) 14 (.ext (.timeUnit u)),
              jh1, hp⟩ := by
      intro k
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
      time_step_blk
      rw [hl8]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hsz_lt, ↓reduceIte]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [hl8]
      rw [runFast_iterator_next hit harr hsz_lt]
      simp only [hidx_toNat, hdrop_pr]
      time_step_blk
      rw [runFast_checkcast_pair]
      time_step_blk
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      rw [runFast_checkcast_ext (by rfl)]
      time_step_blk
      rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
      rw [runFast_checkcast_ext (by rfl)]
      time_step_blk
      rfl
    cases u with
    | timeBased tu =>
      obtain ⟨q, hq, hqMin⟩ := hnm
      have hnz_eval : isNonZeroUnitPair (.timeBased tu, p) = (q != 0) := by
        simp [isNonZeroUnitPair, hq]
      let locsNext := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
        9 (unitPairVal (.timeBased tu) p)) 10 (unitPairVal (.timeBased tu) p)) 11 (.i32 0))
        12 (.ext (.timeUnit (.timeBased tu)))) 13 (.ext (.period p)))
        14 (.ext (.timeUnit (.timeBased tu)))
      have hl4' : locsNext 4 = .heapRef listAddr := by simp [locsNext, setLocal, hl4]
      have hl8' : locsNext 8 = .heapRef itAddr := by simp [locsNext, setLocal, hl8]
      have hl9' : locsNext 9 = unitPairVal (.timeBased tu) p := by simp [locsNext, setLocal]
      have hl12' : locsNext 12 = .ext (.timeUnit (.timeBased tu)) := by simp [locsNext, setLocal]
      have hl13' : locsNext 13 = .ext (.period p) := by simp [locsNext, setLocal]
      have hbody : ∀ k,
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 36)
              PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
              ⟨70, [], locs, jh, hp⟩ =
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 1)
              PeriodUntilKt_periodUntilWithProgressiveUnits_prog 124 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 124)
              ⟨124, [.i32 (if q != 0 then 1 else 0)], locsNext, jh1, hp⟩ := by
        intro k
        rw [show k + 36 = (k + 13) + 23 from by omega, hhead]
        dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
        rw [runFast_instanceof_ext, checkInst_tb_tb]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [runFast_checkcast_ext (by rfl)]
        rw [runFast_call_timeComponentInWholeUnits hext hd1 (by omega) hq hc1]
        rw [runFast_math_absLong]
        time_step_blk
        have hcmp := i64_abs_cmp_pos q hqMin
        by_cases hq0 : q = 0
        · subst hq0
          have hfalse : ((0 : Int64) != 0) = false := by decide
          rw [hfalse] at hcmp
          simp only [hfalse]
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
          simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
            UInt64.toBitVec_zero, hcmp, Bool.not_false, ↓reduceIte]
          time_step_blk
          rfl
        · have htrue : (q != 0) = true := bne_iff_ne.mpr hq0
          rw [htrue] at hcmp
          simp only [htrue, ↓reduceIte]
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
          simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
            UInt64.toBitVec_zero, hcmp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          time_step_blk
      by_cases hq0 : q = 0
      · subst hq0
        have heq_f : isNonZeroUnitPair (.timeBased tu, p) = false := by rw [hnz_eval]; decide
        have hdrop_step :
            (pairs.drop idx).find? isNonZeroUnitPair =
              (pairs.drop (idx + 1)).find? isNonZeroUnitPair := by
          rw [List.drop_eq_getElem_cons hidx_lt, hpr]
          simp [List.find?, heq_f]
        obtain ⟨endSt, hih, hc_ih, hhp_ih⟩ :=
          ih (idx + 1) jh1 locsNext (fuel - 36) (by omega) (by omega) hc1 hlist1 harr1 hit1
            hl4' hl8' hne1 hne2
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 36 ≤ fuel)
        have hloop :
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 36)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locs, jh, hp⟩ =
              Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (fuel - 36)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locsNext, jh1, hp⟩ := by
          rw [hbody]
          dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
          rw [runFast_ifeq_zero]
          have hk_eq : k = fuel - 36 := by omega
          rw [hk_eq]
          rfl
        refine ⟨endSt, ?_, hc_ih, hhp_ih⟩
        simp only [hdrop_step]
        rw [hk, hloop, hih]
      · have htrue : (q != 0) = true := bne_iff_ne.mpr hq0
        have heq_t : isNonZeroUnitPair (.timeBased tu, p) = true := by rw [hnz_eval]; exact htrue
        have hdrop_step :
            (pairs.drop idx).find? isNonZeroUnitPair = some (.timeBased tu, p) := by
          rw [List.drop_eq_getElem_cons hidx_lt, hpr]
          simp [List.find?, heq_t]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 42 ≤ fuel)
        have hret :
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 42)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locs, jh, hp⟩ =
              some (unitPairVal (.timeBased tu) p,
                ⟨135, [unitPairVal (.timeBased tu) p], locsNext, jh1, hp⟩) := by
          rw [show k + 42 = (k + 6) + 36 from by omega, hbody]
          simp only [htrue, ↓reduceIte]
          dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
          rw [runFast_ifeq_nonzero (by decide)]
          time_step_blk
          rw [runFast_checkcast_pair]
          time_step_blk
          rw [runFast_ifnonnull_branch (by rfl)]
          (conv => lhs; tactic => time_norm_run_args)
          rw [runFast_areturn]
          rfl
        refine ⟨⟨135, [unitPairVal (.timeBased tu) p], locsNext, jh1, hp⟩, ?_, hc1, rfl⟩
        simp only [hdrop_step, Option.getD_some]
        rw [hk, hret]
    | dateBased du =>
      obtain ⟨q, hq, hqMin⟩ := hnm
      have hnz_eval : isNonZeroUnitPair (.dateBased du, p) = (q != 0) := by
        simp [isNonZeroUnitPair, hq]
      let locsNext := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
        9 (unitPairVal (.dateBased du) p)) 10 (unitPairVal (.dateBased du) p)) 11 (.i32 0))
        12 (.ext (.timeUnit (.dateBased du)))) 13 (.ext (.period p)))
        14 (.ext (.timeUnit (.dateBased du)))
      have hl4' : locsNext 4 = .heapRef listAddr := by simp [locsNext, setLocal, hl4]
      have hl8' : locsNext 8 = .heapRef itAddr := by simp [locsNext, setLocal, hl8]
      have hl9' : locsNext 9 = unitPairVal (.dateBased du) p := by simp [locsNext, setLocal]
      have hl12' : locsNext 12 = .ext (.timeUnit (.dateBased du)) := by simp [locsNext, setLocal]
      have hl13' : locsNext 13 = .ext (.period p) := by simp [locsNext, setLocal]
      have hbody : ∀ k,
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 37)
              PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
              ⟨70, [], locs, jh, hp⟩ =
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 1)
              PeriodUntilKt_periodUntilWithProgressiveUnits_prog 124 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 124)
              ⟨124, [.i32 (if q != 0 then 1 else 0)], locsNext, jh1, hp⟩ := by
        intro k
        rw [show k + 37 = (k + 14) + 23 from by omega, hhead]
        dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
        rw [runFast_instanceof_ext, checkInst_tb_db]
        rw [runFast_ifeq_zero]
        time_step_blk
        rw [runFast_instanceof_ext, checkInst_db_db]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [runFast_checkcast_ext (by rfl)]
        rw [runFast_call_dateComponentInWholeUnits hext (by omega) (by omega) hq]
        rw [runFast_math_absInt]
        have hcmp := i32_abs_le_zero q hqMin
        by_cases hq0 : q = 0
        · subst hq0
          have hfalse : ((0 : Int32) != 0) = false := by decide
          rw [hfalse] at hcmp
          simp only [hfalse]
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
          simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
            hcmp, Bool.not_false, ↓reduceIte]
          time_step_blk
          rfl
        · have htrue : (q != 0) = true := bne_iff_ne.mpr hq0
          rw [htrue] at hcmp
          simp only [htrue, ↓reduceIte]
          rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
          simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
            hcmp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          time_step_blk
      by_cases hq0 : q = 0
      · subst hq0
        have heq_f : isNonZeroUnitPair (.dateBased du, p) = false := by rw [hnz_eval]; decide
        have hdrop_step :
            (pairs.drop idx).find? isNonZeroUnitPair =
              (pairs.drop (idx + 1)).find? isNonZeroUnitPair := by
          rw [List.drop_eq_getElem_cons hidx_lt, hpr]
          simp [List.find?, heq_f]
        obtain ⟨endSt, hih, hc_ih, hhp_ih⟩ :=
          ih (idx + 1) jh1 locsNext (fuel - 37) (by omega) (by omega) hc1 hlist1 harr1 hit1
            hl4' hl8' hne1 hne2
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 37 ≤ fuel)
        have hloop :
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 37)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locs, jh, hp⟩ =
              Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (fuel - 37)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locsNext, jh1, hp⟩ := by
          rw [hbody]
          dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
          rw [runFast_ifeq_zero]
          have hk_eq : k = fuel - 37 := by omega
          rw [hk_eq]
          rfl
        refine ⟨endSt, ?_, hc_ih, hhp_ih⟩
        simp only [hdrop_step]
        rw [hk, hloop, hih]
      · have htrue : (q != 0) = true := bne_iff_ne.mpr hq0
        have heq_t : isNonZeroUnitPair (.dateBased du, p) = true := by rw [hnz_eval]; exact htrue
        have hdrop_step :
            (pairs.drop idx).find? isNonZeroUnitPair = some (.dateBased du, p) := by
          rw [List.drop_eq_getElem_cons hidx_lt, hpr]
          simp [List.find?, heq_t]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 43 ≤ fuel)
        have hret :
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 43)
                PeriodUntilKt_periodUntilWithProgressiveUnits_prog 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
                ⟨70, [], locs, jh, hp⟩ =
              some (unitPairVal (.dateBased du) p,
                ⟨135, [unitPairVal (.dateBased du) p], locsNext, jh1, hp⟩) := by
          rw [show k + 43 = (k + 6) + 37 from by omega, hbody]
          simp only [htrue, ↓reduceIte]
          dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
          rw [runFast_ifeq_nonzero (by decide)]
          time_step_blk
          rw [runFast_checkcast_pair]
          time_step_blk
          rw [runFast_ifnonnull_branch (by rfl)]
          (conv => lhs; tactic => time_norm_run_args)
          rw [runFast_areturn]
          rfl
        refine ⟨⟨135, [unitPairVal (.dateBased du) p], locsNext, jh1, hp⟩, ?_, hc1, rfl⟩
        simp only [hdrop_step, Option.getD_some]
        rw [hk, hret]

theorem periodUntilWithProgressiveUnits_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 50 ≤ subFuel)
    (start other : Int64) (units : List DateTimeUnit) (tz : String)
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31)
    (hfuel : 70 * units.length + 70 ≤ fuel)
    (hp : TimeHeap)
    (hNotMin : ∀ u ∈ units, periodNoAbsMin (periodUntilWithUnitModel (hp.untilTz start other u tz) u) u)
    (listAddr arrAddr : Nat) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray)) :
    let pairs := units.map fun u => (u, periodUntilWithUnitModel (hp.untilTz start other u tz) u)
    ∃ resPair endSt,
      periodUntilWithProgressiveUnitsModel pairs = some resPair ∧
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntilWithProgressiveUnits_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
          (2, .heapRef listAddr), (3, .ext (.timeZone tz))] hp jh) =
        some (unitPairVal resPair.1 resPair.2, endSt) ∧
      HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 2 ≤ d1 := by omega
  intro pairs
  let resPair := ((pairs.drop 0).find? isNonZeroUnitPair).getD (pairs[pairs.length - 1]'
    (by cases units with | nil => exact absurd rfl hneUnits | cons _ _ => simp [pairs]))
  have hmod : periodUntilWithProgressiveUnitsModel pairs = some resPair := by
    have hneP : pairs ≠ [] := by simp [pairs, hneUnits]
    simpa [resPair, List.drop_zero] using isNonZeroUnitPair_eq_model pairs hneP
  refine ⟨resPair, ?_⟩
  let newArrAddr := jh.objects.size
  let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let newListAddr := jh.objects.size + 1
  let jh2 := (jh1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)])).2
  let itAddr := jh.objects.size + 2
  let jh3 := (jh2.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])).2
  have harrLt : arrAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp harr).1
  have hlistLt : listAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hlist).1
  have hsz1 : jh1.objects.size = jh.objects.size + 1 := by simp [jh1, Jvm.JvmHeap.alloc]
  have hsz2 : jh2.objects.size = jh.objects.size + 2 := by simp [jh2, jh1, Jvm.JvmHeap.alloc]
  have hlist_jh1 : jh1.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
    dsimp only [jh1]; rw [jvmHeap_get_alloc_lt jh _ hlistLt]; exact hlist
  have harr_jh1 : jh1.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) := by
    dsimp only [jh1]; rw [jvmHeap_get_alloc_lt jh _ harrLt]; exact harr
  have hlist_jh2 : jh2.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
    dsimp only [jh2]; rw [jvmHeap_get_alloc_lt jh1 _ (by omega)]; exact hlist_jh1
  have harr_jh2 : jh2.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) := by
    dsimp only [jh2]; rw [jvmHeap_get_alloc_lt jh1 _ (by omega)]; exact harr_jh1
  have hnewArr_jh2 : jh2.get? newArrAddr = some (.objArray "java/lang/Object" #[]) := by
    dsimp only [jh2, jh1, newArrAddr]
    rw [jvmHeap_get_alloc_lt jh1 _ (by omega), jvmHeap_get_alloc_self]
  have hnewList_jh2 : jh2.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh2, newListAddr]
    rw [← hsz1]
    exact jvmHeap_get_alloc_self jh1 _
  have harr_jh3 : jh3.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit" (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact harr_jh2
  have hnewArr_jh3 : jh3.get? newArrAddr = some (.objArray "java/lang/Object" #[]) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact hnewArr_jh2
  have hnewList_jh3 : jh3.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact hnewList_jh2
  have hit_jh3 : jh3.get? itAddr =
      some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat 0))]) := by
    dsimp only [jh3, itAddr]
    rw [← hsz2]
    exact jvmHeap_get_alloc_self jh2 _
  let locs3 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (fun _ => Jvm.JvmVal.i32 0) 0 (.ext (TimeExt.instant start))) 1 (.ext (TimeExt.instant other)))
    2 (.heapRef listAddr)) 3 (.ext (TimeExt.timeZone tz)))
    5 (.heapRef listAddr)) 6 (.i32 0)) 7 (.heapRef listAddr))
    8 (.heapRef newListAddr)) 9 (.i32 0)
  let locs3' := setLocal locs3 10 (.heapRef itAddr)
  have hl0 : locs3' 0 = .ext (.instant start) := by simp [locs3', locs3, setLocal]
  have hl1 : locs3' 1 = .ext (.instant other) := by simp [locs3', locs3, setLocal]
  have hl3 : locs3' 3 = .ext (.timeZone tz) := by simp [locs3', locs3, setLocal]
  have hl8 : locs3' 8 = .heapRef newListAddr := by simp [locs3', locs3, setLocal]
  have hl10 : locs3' 10 = .heapRef itAddr := by simp [locs3', locs3, setLocal]
  have hc3 : HasTimeStaticsClean jh3 :=
    jvmHeap_staticsClean_alloc (jvmHeap_staticsClean_alloc (jvmHeap_staticsClean_alloc hc _) _) _
  let kFind := fuel - 33 - (3 + 25 * units.length)
  obtain ⟨jhEnd, locsEnd, hEndList, hEndArr, hcEnd, hlEnd8, hEndArrLt, hEndListLt, hMap⟩ :=
    progressiveMapLoop_equiv resolveProg hext (d1 := d1) (subFuel := subFuel) (by omega) hsf start other units tz
      arrAddr newArrAddr newListAddr itAddr hp units.length 0 #[] jh3 locs3' kFind (by omega)
      harr_jh3 hit_jh3 hnewList_jh3 hnewArr_jh3 hl0 hl1 hl3 hl8 hl10
      (by omega) (by omega) (by omega) (by omega) (by omega) hlen31
  have hcEnd' : HasTimeStaticsClean jhEnd := hcEnd hc3
  let it2Addr := jhEnd.objects.size
  let jh4 := (jhEnd.alloc (.instance "java/util/Iterator" [("arr", .heapRef newArrAddr), ("idx", .i32 0)])).2
  have hc4 : HasTimeStaticsClean jh4 := jvmHeap_staticsClean_alloc hcEnd' _
  have hEndArr' : jhEnd.get? newArrAddr =
      some (.objArray "java/lang/Object" (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray) := by
    rw [hEndArr]; simp [pairs]
  have hlist_jh4 : jh4.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh4]; rw [jvmHeap_get_alloc_lt jhEnd _ hEndListLt]; exact hEndList
  have harr_jh4 : jh4.get? newArrAddr =
      some (.objArray "java/lang/Object" (pairs.map fun pr => unitPairVal pr.1 pr.2).toArray) := by
    dsimp only [jh4]; rw [jvmHeap_get_alloc_lt jhEnd _ hEndArrLt]; exact hEndArr'
  have hit_jh4 : jh4.get? it2Addr =
      some (.instance "java/util/Iterator" [("arr", .heapRef newArrAddr), ("idx", .i32 (UInt32.ofNat 0))]) := by
    dsimp only [jh4, it2Addr]
    exact jvmHeap_get_alloc_self jhEnd _
  let locs4 := setLocal (setLocal (setLocal (setLocal locsEnd
    4 (.heapRef newListAddr)) 6 (.heapRef newListAddr)) 7 (.i32 0)) 8 (.heapRef it2Addr)
  have hnePairs : pairs ≠ [] := by simp [pairs, hneUnits]
  have hlenPairs31 : pairs.length < 2 ^ 31 := by simpa [pairs] using hlen31
  have hNotMinP : ∀ pr ∈ pairs, periodNoAbsMin pr.2 pr.1 := by
    intro pr hmem
    simp only [pairs, List.mem_map] at hmem
    obtain ⟨u, hu, rfl⟩ := hmem
    exact hNotMin u hu
  obtain ⟨endSt, hFind, hcEndSt, hhpEndSt⟩ :=
    progressiveFindLoop_equiv resolveProg hext hd1 hsf pairs hnePairs hlenPairs31 hNotMinP
      newArrAddr newListAddr it2Addr hp pairs.length 0 jh4 locs4 (kFind - 12)
      (by omega) (by simp [pairs]; dsimp only [kFind]; omega) hc4 hlist_jh4 harr_jh4 hit_jh4
      (by simp [locs4, setLocal]) (by simp [locs4, setLocal]) (by omega) (by omega)
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) fuel
          PeriodUntilKt_periodUntilWithProgressiveUnits_prog 0 PeriodUntilKt_periodUntilWithProgressiveUnits_prog
          (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
            (2, .heapRef listAddr), (3, .ext (.timeZone tz))] hp jh) =
        some (unitPairVal resPair.1 resPair.2, endSt) := by
    have hsplit : fuel = (kFind + 3 + 25 * units.length) + 33 := by dsimp only [kFind]; omega
    rw [hsplit]
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkcast_arrayList hlist]
    time_step_blk
    rw [runFast_newClass]
    time_step_blk
    rw [runFast_collectionSizeOrDefault hlist harr]
    rw [runFast_arrayList_init (ui32_ofNat_nonneg_of_lt (by simp [hlen31]))]
    rw [runFast_checkcast_arrayList hnewList_jh2]
    time_step_blk
    rw [runFast_iterable_iterator hlist_jh2 harr_jh2]
    rw [runFast_astore]
    rw [hsz2]
    change Jvm.runJvmResFast _ (kFind + 3 + 25 * units.length) _ 33
      (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 33) ⟨33, [], locs3', jh3, hp⟩ = _
    rw [hMap]
    obtain ⟨kRem, hkRem⟩ := Nat.exists_eq_add_of_le' (by dsimp only [kFind]; omega : 12 ≤ kFind)
    rw [hkRem]
    dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_prog, List.drop]
    time_step_blk
    rw [hlEnd8]
    rw [runFast_checkcast_arrayList hEndList]
    time_step_blk
    rw [runFast_checkcast_arrayList hEndList]
    time_step_blk
    rw [runFast_iterable_iterator hEndList hEndArr']
    rw [runFast_astore]
    have hk_eq : kRem = kFind - 12 := by dsimp only [kFind]; omega
    rw [hk_eq]
    change Jvm.runJvmResFast _ (kFind - 12) _ 70 (PeriodUntilKt_periodUntilWithProgressiveUnits_prog.drop 70)
      ⟨70, [], locs4, jh4, hp⟩ = _
    exact hFind
  exact ⟨endSt, hmod, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrun, hcEndSt, hhpEndSt⟩

theorem progressiveMapLoopTime_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel : Nat} (hd1 : 1 ≤ d1) (hsf : 50 ≤ subFuel)
    (start other : Int64) (units : List TimeBasedUnit)
    (arrAddr newArrAddr newListAddr itAddr : Nat)
    (hp : TimeHeap) :
    ∀ rem : Nat, ∀ idx : Nat, ∀ acc : Array JvmVal, ∀ jh : Jvm.JvmHeap TimeExt,
      ∀ locs : Nat → JvmVal, ∀ k : Nat,
      idx + rem = units.length →
      jh.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
          (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) →
      jh.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]) →
      jh.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) →
      jh.get? newArrAddr = some (.objArray "java/lang/Object" acc) →
      locs 0 = .ext (.instant start) →
      locs 1 = .ext (.instant other) →
      locs 7 = .heapRef newListAddr →
      locs 9 = .heapRef itAddr →
      itAddr ≠ newArrAddr → itAddr ≠ newListAddr → itAddr ≠ arrAddr →
      newArrAddr ≠ arrAddr → newArrAddr ≠ newListAddr →
      units.length < 2 ^ 31 →
      ∃ jhEnd locsEnd,
        (jhEnd.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) ∧
        jhEnd.get? newArrAddr = some (.objArray "java/lang/Object"
          (acc ++ ((units.drop idx).map fun u =>
            unitTimePairVal u (periodUntilWithUnitTimeModel (hp.untilTime start other u) u)).toArray)) ∧
        (HasTimeStaticsClean jh → HasTimeStaticsClean jhEnd) ∧
        locsEnd 7 = .heapRef newListAddr ∧
        newArrAddr < jhEnd.objects.size ∧ newListAddr < jhEnd.objects.size ∧
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 3 + 24 * rem)
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 30 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 30)
            ⟨30, [], locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) k
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 54 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 54)
            ⟨54, [], locsEnd, jhEnd, hp⟩) := by
  intro rem
  induction rem with
  | zero =>
    intro idx acc jh locs k hlen harr hit hlist hnewArr hl0 hl1 hl7 hl9
      hne1 hne2 hne3 hne4 hne5 hlen31
    have hidx_eq : idx = units.length := by omega
    subst hidx_eq
    have hnewArrLt : newArrAddr < jh.objects.size :=
      (Array.getElem?_eq_some_iff.mp hnewArr).1
    have hnewListLt : newListAddr < jh.objects.size :=
      (Array.getElem?_eq_some_iff.mp hlist).1
    refine ⟨jh, locs, hlist, ?_, fun hc => hc, hl7, hnewArrLt, hnewListLt, ?_⟩
    · simp [List.drop_length, hnewArr]
    · have h1 : (UInt32.ofNat units.length).toNat = units.length := by
        simp [Nat.mod_eq_of_lt (by omega : units.length < 2 ^ 32)]
      have hlt_false : ¬ (UInt32.ofNat units.length).toNat <
          (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray.size := by
        simp [h1]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
      time_step_blk
      rw [hl9]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hlt_false, ↓reduceIte]
      rw [runFast_ifeq_zero]
  | succ r ih =>
    intro idx acc jh locs k hlen harr hit hlist hnewArr hl0 hl1 hl7 hl9
      hne1 hne2 hne3 hne4 hne5 hlen31
    have hidx_lt : idx < units.length := by omega
    have hidx_toNat : (UInt32.ofNat idx).toNat = idx := by
      simp [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)]
    have hitLt : itAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hit).1
    have hnewArrLt : newArrAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hnewArr).1
    let u := units[idx]
    let p := periodUntilWithUnitTimeModel (hp.untilTime start other u) u
    let pairV := unitTimePairVal u p
    let jh1 := jh.set itAddr
      (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx + 1))])
    let jh2 := jh1.set newArrAddr (.objArray "java/lang/Object" (acc.push pairV))
    have hidx_u32 : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
      rw [UInt32.ofNat_add]; rfl
    have harr1 : jh1.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
          (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne3]; exact harr
    have hlist1 : jh1.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne2]; exact hlist
    have hnewArr1 : jh1.get? newArrAddr = some (.objArray "java/lang/Object" acc) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne1]; exact hnewArr
    have harr2 : jh2.get? arrAddr =
        some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
          (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) := by
      dsimp only [jh2]; rw [jvmHeap_get_set_ne hne4]; exact harr1
    have hlist2 : jh2.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
      dsimp only [jh2]; rw [jvmHeap_get_set_ne hne5]; exact hlist1
    have hnewArr2 : jh2.get? newArrAddr = some (.objArray "java/lang/Object" (acc.push pairV)) := by
      dsimp only [jh2]; exact jvmHeap_get_set_same (by rw [jvmHeap_set_size]; exact hnewArrLt)
    have hit2 : jh2.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))]) := by
      dsimp only [jh2, jh1]
      rw [jvmHeap_get_set_ne (Ne.symm hne1), jvmHeap_get_set_same hitLt, hidx_u32]
    let locs1 := setLocal (setLocal (setLocal (setLocal locs
      10 (.ext (.timeUnit (.timeBased u)))) 11 (.ext (.timeUnit (.timeBased u)))) 13 (.heapRef newListAddr)) 12 (.i32 0)
    have hlocs_step :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) ((k + 3 + 24 * r) + 24)
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 30 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 30)
            ⟨30, [], locs, jh, hp⟩ =
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 3 + 24 * r)
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 30 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 30)
            ⟨30, [], locs1, jh2, hp⟩ := by
      have hdrop_u : (units.map fun x => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased x))).toArray[idx]'(by simp [hidx_lt]) =
          .ext (.timeUnit (.timeBased u)) := by
        simp [u]
      have hsz_lt : (UInt32.ofNat idx).toNat <
          (units.map fun x => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased x))).toArray.size := by
        simp [hidx_toNat, hidx_lt]
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
      time_step_blk
      rw [hl9]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hsz_lt, ↓reduceIte]
      rw [runFast_ifeq_nonzero (by decide)]
      time_step_blk
      rw [hl9]
      rw [runFast_iterator_next hit harr hsz_lt]
      simp only [hidx_toNat, hdrop_u]
      time_step_blk
      rw [hl7]
      time_step_blk
      rw [runFast_checkcast_ext (by rfl)]
      time_step_blk
      rw [hl0, hl1]
      rw [runFast_call_periodUntilWithUnit_1 hext hd1 (by omega)]
      rw [runFast_tuples_to]
      time_step_blk
      rw [runFast_arrayList_add hlist1 hnewArr1]
      time_step_blk
      rw [runFast_goto]
      rfl
    have h0_1 : locs1 0 = .ext (.instant start) := by simp [locs1, setLocal, hl0]
    have h1_1 : locs1 1 = .ext (.instant other) := by simp [locs1, setLocal, hl1]
    have h7_1 : locs1 7 = .heapRef newListAddr := by simp [locs1, setLocal, hl7]
    have h9_1 : locs1 9 = .heapRef itAddr := by simp [locs1, setLocal, hl9]
    obtain ⟨jhEnd, locsEnd, h1, h2, h3, h4, h5, h6, hrun_ih⟩ :=
      ih (idx + 1) (acc.push pairV) jh2 locs1 k (by omega) harr2 hit2 hlist2 hnewArr2
        h0_1 h1_1 h7_1 h9_1 hne1 hne2 hne3 hne4 hne5 hlen31
    refine ⟨jhEnd, locsEnd, h1, ?_, fun hc => h3 (jvmHeap_staticsClean_set (jvmHeap_staticsClean_set hc _ _) _ _),
      h4, h5, h6, ?_⟩
    · rw [h2, List.drop_eq_getElem_cons hidx_lt]
      simp [u, p, pairV]
      rw [List.drop_eq_getElem_cons (i := idx)
        (l := List.map (fun u => unitTimePairVal u (periodUntilWithUnitTimeModel (hp.untilTime start other u) u)) units)
        (by simp [hidx_lt])]
      simp
    · rw [show k + 3 + 24 * (r + 1) = (k + 3 + 24 * r) + 24 from by omega]
      rw [hlocs_step, hrun_ih]

def isNonZeroTimePair (pr : TimeBasedUnit × DateTimePeriodModel) : Bool :=
  match timeComponentInWholeUnitsModel pr.2 pr.1 with
  | some v => v != 0
  | none => false

theorem isNonZeroTimePair_eq_model (pairs : List (TimeBasedUnit × DateTimePeriodModel))
    (hnePairs : pairs ≠ []) :
    (periodUntilWithProgressiveUnitsTimeModel pairs) =
      some ((pairs.find? isNonZeroTimePair).getD (pairs[pairs.length - 1]'
        (by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp))) := by
  change (match pairs.find? isNonZeroTimePair with
    | some pair => some pair
    | none => pairs.getLast?) = _
  cases hf : pairs.find? isNonZeroTimePair with
  | some pr => rfl
  | none =>
    have hpos : 0 < pairs.length := by
      cases pairs with
      | nil => exact absurd rfl hnePairs
      | cons _ _ => simp
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl

/-- Domain of `periodUntilWithProgressiveUnits` for `TimeBased` units: every period has a whole number of its unit
other than `Long.MIN_VALUE` (where `abs` overflows). -/
def timePeriodNoAbsMin (p : DateTimePeriodModel) (tu : TimeBasedUnit) : Prop :=
  ∃ q, timeComponentInWholeUnitsModel p tu = some q ∧ q ≠ (-9223372036854775808 : Int64)

theorem progressiveFindLoopTime_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    {d1 subFuel : Nat} (hd1 : 2 ≤ d1) (hsf : 50 ≤ subFuel)
    (pairs : List (TimeBasedUnit × DateTimePeriodModel))
    (hnePairs : pairs ≠ []) (hlen31 : pairs.length < 2 ^ 31)
    (hNotMin : ∀ pr ∈ pairs, timePeriodNoAbsMin pr.2 pr.1)
    (arrAddr listAddr itAddr : Nat) (hp : TimeHeap) :
    ∀ rem : Nat, ∀ idx : Nat, ∀ jh : Jvm.JvmHeap TimeExt,
      ∀ locs : Nat → JvmVal, ∀ fuel : Nat,
      idx + rem = pairs.length →
      36 * rem + 20 ≤ fuel →
      HasTimeStaticsClean jh →
      jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) →
      jh.get? arrAddr =
        some (.objArray "java/lang/Object" (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray) →
      jh.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx))]) →
      locs 3 = .heapRef listAddr →
      locs 7 = .heapRef itAddr →
      itAddr ≠ arrAddr → itAddr ≠ listAddr →
      let resPair := ((pairs.drop idx).find? isNonZeroTimePair).getD (pairs[pairs.length - 1]'
        (by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp))
      ∃ endSt,
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) fuel
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
            ⟨66, [], locs, jh, hp⟩ =
          some (unitTimePairVal resPair.1 resPair.2, endSt) ∧
        HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  intro rem
  induction rem with
  | zero =>
    intro idx jh locs fuel hlen hfuel hc hlist harr hit hl3 hl7 hne1 hne2
    have hidx_eq : idx = pairs.length := by omega
    subst hidx_eq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 15 ≤ fuel)
    have hpos : 0 < (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray.size := by
      cases pairs with
      | nil => exact absurd rfl hnePairs
      | cons _ _ => simp
    have hlast : (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray[
        (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray.size - 1] =
        unitTimePairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
          (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2 := by
      simp [unitTimePairVal]
    have h1 : (UInt32.ofNat pairs.length).toNat = pairs.length := by
      simp [Nat.mod_eq_of_lt (by omega : pairs.length < 2 ^ 32)]
    have hlt_false : ¬ (UInt32.ofNat pairs.length).toNat <
        (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray.size := by
      simp [h1]
    have hres :
        Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 15)
            PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
            ⟨66, [], locs, jh, hp⟩ =
          some (unitTimePairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
              (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2,
            ⟨106,
              [unitTimePairVal (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).1
                (pairs[pairs.length - 1]'(by cases pairs with | nil => exact absurd rfl hnePairs | cons _ _ => simp)).2],
              locs, jh, hp⟩) := by
      conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
      time_step_blk
      rw [hl7]
      rw [runFast_iterator_hasNext hit harr]
      simp only [hlt_false, ↓reduceIte]
      rw [runFast_ifeq_zero]
      time_step_blk
      rw [runFast_checkcast_null]
      time_step_blk
      rw [runFast_ifnonnull_fallthrough]
      time_step_blk
      rw [hl3]
      rw [runFast_collections_last hlist harr hpos]
      rw [hlast]
      dsimp only [unitTimePairVal]
      rw [runFast_checkcast_pair]
      rw [runFast_areturn]
    have hdrop : (pairs.drop pairs.length).find? isNonZeroTimePair = none := by
      simp [List.drop_length]
    simp only [hdrop, Option.getD_none]
    exact ⟨_, hres, hc, rfl⟩
  | succ r ih =>
    intro idx jh locs fuel hlen hfuel hc hlist harr hit hl3 hl7 hne1 hne2
    have hidx_lt : idx < pairs.length := by omega
    have hidx_toNat : (UInt32.ofNat idx).toNat = idx := by
      simp [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)]
    have hitLt : itAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hit).1
    obtain ⟨⟨tu, p⟩, hpr⟩ : ∃ pr, pairs[idx] = pr := ⟨_, rfl⟩
    let jh1 := jh.set itAddr
      (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat idx + 1))])
    have hidx_u32 : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
      rw [UInt32.ofNat_add]; rfl
    have hlist1 : jh1.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne2]; exact hlist
    have harr1 : jh1.get? arrAddr =
        some (.objArray "java/lang/Object" (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_ne hne1]; exact harr
    have hit1 : jh1.get? itAddr =
        some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))]) := by
      dsimp only [jh1]; rw [jvmHeap_get_set_same hitLt, hidx_u32]
    have hsz_lt : (UInt32.ofNat idx).toNat <
        (pairs.map fun x => unitTimePairVal x.1 x.2).toArray.size := by
      simp [hidx_toNat, hidx_lt]
    have hdrop_pr : (pairs.map fun x => unitTimePairVal x.1 x.2).toArray[idx]'(by simp [hidx_lt]) =
        unitTimePairVal tu p := by
      simp [hpr, unitTimePairVal]
    have hc1 : HasTimeStaticsClean jh1 := jvmHeap_staticsClean_set hc _ _
    obtain ⟨q, hq, hqMin⟩ : timePeriodNoAbsMin p tu := hNotMin (tu, p) (hpr ▸ List.getElem_mem hidx_lt)
    have hnz_eval : isNonZeroTimePair (tu, p) = (q != 0) := by
      simp [isNonZeroTimePair, hq]
    let locsNext := setLocal (setLocal (setLocal (setLocal (setLocal locs
      8 (unitTimePairVal tu p)) 9 (unitTimePairVal tu p)) 10 (.i32 0))
      11 (.ext (.timeUnit (.timeBased tu)))) 12 (.ext (.period p))
    have hl3' : locsNext 3 = .heapRef listAddr := by simp [locsNext, setLocal, hl3]
    have hl7' : locsNext 7 = .heapRef itAddr := by simp [locsNext, setLocal, hl7]
    have hcmp := i64_abs_cmp_pos q hqMin
    by_cases hq0 : q = 0
    · subst hq0
      have heq_f : isNonZeroTimePair (tu, p) = false := by rw [hnz_eval]; decide
      have hdrop_step :
          (pairs.drop idx).find? isNonZeroTimePair =
            (pairs.drop (idx + 1)).find? isNonZeroTimePair := by
        rw [List.drop_eq_getElem_cons hidx_lt, hpr]
        simp [List.find?, heq_f]
      have hfalse : ((0 : Int64) != 0) = false := by decide
      rw [hfalse] at hcmp
      obtain ⟨endSt, hih, hc_ih, hhp_ih⟩ :=
        ih (idx + 1) jh1 locsNext (fuel - 28) (by omega) (by omega) hc1 hlist1 harr1 hit1
          hl3' hl7' hne1 hne2
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 28 ≤ fuel)
      have hloop :
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 28)
              PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
              ⟨66, [], locs, jh, hp⟩ =
            Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) k
              PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
              ⟨66, [], locsNext, jh1, hp⟩ := by
        conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
        time_step_blk
        rw [hl7]
        rw [runFast_iterator_hasNext hit harr]
        simp only [hsz_lt, ↓reduceIte]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [hl7]
        rw [runFast_iterator_next hit harr hsz_lt]
        simp only [hidx_toNat, hdrop_pr]
        time_step_blk
        rw [runFast_checkcast_pair]
        time_step_blk
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        rw [runFast_checkcast_ext (by rfl)]
        time_step_blk
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        rw [runFast_checkcast_ext (by rfl)]
        time_step_blk
        rw [runFast_call_timeComponentInWholeUnits hext hd1 (by omega) hq hc1]
        rw [runFast_math_absLong]
        time_step_blk
        rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
        simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
          UInt64.toBitVec_zero, hcmp, Bool.not_false, ↓reduceIte]
        time_step_blk
        rw [runFast_ifeq_zero]
        rfl
      refine ⟨endSt, ?_, hc_ih, hhp_ih⟩
      simp only [hdrop_step]
      have hk_eq : fuel = k + 28 := by omega
      rw [hk_eq, hloop, show k = fuel - 28 by omega, hih]
    · have htrue : (q != 0) = true := bne_iff_ne.mpr hq0
      have heq_t : isNonZeroTimePair (tu, p) = true := by rw [hnz_eval]; exact htrue
      have hdrop_step :
          (pairs.drop idx).find? isNonZeroTimePair = some (tu, p) := by
        rw [List.drop_eq_getElem_cons hidx_lt, hpr]
        simp [List.find?, heq_t]
      rw [htrue] at hcmp
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (by omega : 35 ≤ fuel)
      have hret :
          Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) (k + 35)
              PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
              ⟨66, [], locs, jh, hp⟩ =
            some (unitTimePairVal tu p,
              ⟨106, [unitTimePairVal tu p], locsNext, jh1, hp⟩) := by
        conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
        time_step_blk
        rw [hl7]
        rw [runFast_iterator_hasNext hit harr]
        simp only [hsz_lt, ↓reduceIte]
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [hl7]
        rw [runFast_iterator_next hit harr hsz_lt]
        simp only [hidx_toNat, hdrop_pr]
        time_step_blk
        rw [runFast_checkcast_pair]
        time_step_blk
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        rw [runFast_checkcast_ext (by rfl)]
        time_step_blk
        rw [Jvm.runJvmResFast_invokevirtual_step _ (by rfl)]
        rw [runFast_checkcast_ext (by rfl)]
        time_step_blk
        rw [runFast_call_timeComponentInWholeUnits hext hd1 (by omega) hq hc1]
        rw [runFast_math_absLong]
        time_step_blk
        rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
        simp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.asI32?,
          UInt64.toBitVec_zero, hcmp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        time_step_blk
        rw [runFast_ifeq_nonzero (by decide)]
        time_step_blk
        rw [runFast_checkcast_pair]
        time_step_blk
        rw [runFast_ifnonnull_branch (by rfl)]
        (conv => lhs; tactic => time_norm_run_args)
        rw [runFast_areturn]
        rfl
      refine ⟨⟨106, [unitTimePairVal tu p], locsNext, jh1, hp⟩, ?_, hc1, rfl⟩
      simp only [hdrop_step, Option.getD_some]
      rw [hk, hret]

theorem periodUntilWithProgressiveUnits_1_equiv (resolveProg : String → Option (List JvmInstr))
    (hext : ExtendsTimeProgs resolveProg)
    (d subFuel fuel : Nat) (hd : 3 ≤ d) (hsf : 50 ≤ subFuel)
    (start other : Int64) (units : List TimeBasedUnit)
    (hneUnits : units ≠ []) (hlen31 : units.length < 2 ^ 31)
    (hfuel : 70 * units.length + 70 ≤ fuel)
    (hp : TimeHeap)
    (hNotMin : ∀ u ∈ units, timePeriodNoAbsMin (periodUntilWithUnitTimeModel (hp.untilTime start other u) u) u)
    (listAddr arrAddr : Nat) (jh : Jvm.JvmHeap TimeExt)
    (hc : HasTimeStaticsClean jh)
    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
    (harr : jh.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray)) :
    let pairs := units.map fun u => (u, periodUntilWithUnitTimeModel (hp.untilTime start other u) u)
    ∃ resPair endSt,
      periodUntilWithProgressiveUnitsTimeModel pairs = some resPair ∧
      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog
        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
          (2, .heapRef listAddr)] hp jh) =
        some (unitTimePairVal resPair.1 resPair.2, endSt) ∧
      HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ d)
  have hd1 : 2 ≤ d1 := by omega
  intro pairs
  let resPair := ((pairs.drop 0).find? isNonZeroTimePair).getD (pairs[pairs.length - 1]'
    (by cases units with | nil => exact absurd rfl hneUnits | cons _ _ => simp [pairs]))
  have hmod : periodUntilWithProgressiveUnitsTimeModel pairs = some resPair := by
    have hneP : pairs ≠ [] := by simp [pairs, hneUnits]
    simpa [resPair, List.drop_zero] using isNonZeroTimePair_eq_model pairs hneP
  refine ⟨resPair, ?_⟩
  let newArrAddr := jh.objects.size
  let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let newListAddr := jh.objects.size + 1
  let jh2 := (jh1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)])).2
  let itAddr := jh.objects.size + 2
  let jh3 := (jh2.alloc (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 0)])).2
  have harrLt : arrAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp harr).1
  have hlistLt : listAddr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hlist).1
  have hsz1 : jh1.objects.size = jh.objects.size + 1 := by simp [jh1, Jvm.JvmHeap.alloc]
  have hsz2 : jh2.objects.size = jh.objects.size + 2 := by simp [jh2, jh1, Jvm.JvmHeap.alloc]
  have hlist_jh1 : jh1.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
    dsimp only [jh1]; rw [jvmHeap_get_alloc_lt jh _ hlistLt]; exact hlist
  have harr_jh1 : jh1.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) := by
    dsimp only [jh1]; rw [jvmHeap_get_alloc_lt jh _ harrLt]; exact harr
  have hlist_jh2 : jh2.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]) := by
    dsimp only [jh2]; rw [jvmHeap_get_alloc_lt jh1 _ (by omega)]; exact hlist_jh1
  have harr_jh2 : jh2.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) := by
    dsimp only [jh2]; rw [jvmHeap_get_alloc_lt jh1 _ (by omega)]; exact harr_jh1
  have hnewArr_jh2 : jh2.get? newArrAddr = some (.objArray "java/lang/Object" #[]) := by
    dsimp only [jh2, jh1, newArrAddr]
    rw [jvmHeap_get_alloc_lt jh1 _ (by omega), jvmHeap_get_alloc_self]
  have hnewList_jh2 : jh2.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh2, newListAddr]
    rw [← hsz1]
    exact jvmHeap_get_alloc_self jh1 _
  have harr_jh3 : jh3.get? arrAddr =
      some (.objArray "kotlinx/datetime/DateTimeUnit$TimeBased"
        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact harr_jh2
  have hnewArr_jh3 : jh3.get? newArrAddr = some (.objArray "java/lang/Object" #[]) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact hnewArr_jh2
  have hnewList_jh3 : jh3.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh3]; rw [jvmHeap_get_alloc_lt jh2 _ (by omega)]; exact hnewList_jh2
  have hit_jh3 : jh3.get? itAddr =
      some (.instance "java/util/Iterator" [("arr", .heapRef arrAddr), ("idx", .i32 (UInt32.ofNat 0))]) := by
    dsimp only [jh3, itAddr]
    rw [← hsz2]
    exact jvmHeap_get_alloc_self jh2 _
  let locs3 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (fun _ => Jvm.JvmVal.i32 0) 0 (.ext (TimeExt.instant start))) 1 (.ext (TimeExt.instant other)))
    2 (.heapRef listAddr))
    4 (.heapRef listAddr)) 5 (.i32 0)) 6 (.heapRef listAddr))
    7 (.heapRef newListAddr)) 8 (.i32 0)
  let locs3' := setLocal locs3 9 (.heapRef itAddr)
  have hl0 : locs3' 0 = .ext (.instant start) := by simp [locs3', locs3, setLocal]
  have hl1 : locs3' 1 = .ext (.instant other) := by simp [locs3', locs3, setLocal]
  have hl7 : locs3' 7 = .heapRef newListAddr := by simp [locs3', locs3, setLocal]
  have hl9 : locs3' 9 = .heapRef itAddr := by simp [locs3', locs3, setLocal]
  have hc3 : HasTimeStaticsClean jh3 :=
    jvmHeap_staticsClean_alloc (jvmHeap_staticsClean_alloc (jvmHeap_staticsClean_alloc hc _) _) _
  let kFind := fuel - 30 - (3 + 24 * units.length)
  obtain ⟨jhEnd, locsEnd, hEndList, hEndArr, hcEnd, hlEnd7, hEndArrLt, hEndListLt, hMap⟩ :=
    progressiveMapLoopTime_equiv resolveProg hext (d1 := d1) (subFuel := subFuel) (by omega) hsf start other units
      arrAddr newArrAddr newListAddr itAddr hp units.length 0 #[] jh3 locs3' kFind (by omega)
      harr_jh3 hit_jh3 hnewList_jh3 hnewArr_jh3 hl0 hl1 hl7 hl9
      (by omega) (by omega) (by omega) (by omega) (by omega) hlen31
  have hcEnd' : HasTimeStaticsClean jhEnd := hcEnd hc3
  let it2Addr := jhEnd.objects.size
  let jh4 := (jhEnd.alloc (.instance "java/util/Iterator" [("arr", .heapRef newArrAddr), ("idx", .i32 0)])).2
  have hc4 : HasTimeStaticsClean jh4 := jvmHeap_staticsClean_alloc hcEnd' _
  have hEndArr' : jhEnd.get? newArrAddr =
      some (.objArray "java/lang/Object" (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray) := by
    rw [hEndArr]; simp [pairs]
  have hlist_jh4 : jh4.get? newListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef newArrAddr)]) := by
    dsimp only [jh4]; rw [jvmHeap_get_alloc_lt jhEnd _ hEndListLt]; exact hEndList
  have harr_jh4 : jh4.get? newArrAddr =
      some (.objArray "java/lang/Object" (pairs.map fun pr => unitTimePairVal pr.1 pr.2).toArray) := by
    dsimp only [jh4]; rw [jvmHeap_get_alloc_lt jhEnd _ hEndArrLt]; exact hEndArr'
  have hit_jh4 : jh4.get? it2Addr =
      some (.instance "java/util/Iterator" [("arr", .heapRef newArrAddr), ("idx", .i32 (UInt32.ofNat 0))]) := by
    dsimp only [jh4, it2Addr]
    exact jvmHeap_get_alloc_self jhEnd _
  let locs4 := setLocal (setLocal (setLocal (setLocal locsEnd
    3 (.heapRef newListAddr)) 5 (.heapRef newListAddr)) 6 (.i32 0)) 7 (.heapRef it2Addr)
  have hnePairs : pairs ≠ [] := by simp [pairs, hneUnits]
  have hlenPairs31 : pairs.length < 2 ^ 31 := by simpa [pairs] using hlen31
  have hNotMinP : ∀ pr ∈ pairs, timePeriodNoAbsMin pr.2 pr.1 := by
    intro pr hmem
    simp only [pairs, List.mem_map] at hmem
    obtain ⟨u, hu, rfl⟩ := hmem
    exact hNotMin u hu
  obtain ⟨endSt, hFind, hcEndSt, hhpEndSt⟩ :=
    progressiveFindLoopTime_equiv resolveProg hext hd1 hsf pairs hnePairs hlenPairs31 hNotMinP
      newArrAddr newListAddr it2Addr hp pairs.length 0 jh4 locs4 (kFind - 12)
      (by omega) (by simp [pairs]; dsimp only [kFind]; omega) hc4 hlist_jh4 harr_jh4 hit_jh4
      (by simp [locs4, setLocal]) (by simp [locs4, setLocal]) (by omega) (by omega)
  have hrun :
      Jvm.runJvmResFast (mkTimeHooks resolveProg (d1 + 1) subFuel) fuel
          PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog 0 PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog
          (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
            (2, .heapRef listAddr)] hp jh) =
        some (unitTimePairVal resPair.1 resPair.2, endSt) := by
    have hsplit : fuel = (kFind + 3 + 24 * units.length) + 30 := by dsimp only [kFind]; omega
    rw [hsplit]
    simp only [initTimeJvmState, Jvm.initJvmState, List.foldl_cons, List.foldl_nil]
    conv => lhs; arg 5; dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkNotNull (by rfl)]
    time_step_blk
    rw [runFast_checkcast_arrayList hlist]
    time_step_blk
    rw [runFast_newClass]
    time_step_blk
    rw [runFast_collectionSizeOrDefault hlist harr]
    rw [runFast_arrayList_init (ui32_ofNat_nonneg_of_lt (by simp [hlen31]))]
    rw [runFast_checkcast_arrayList hnewList_jh2]
    time_step_blk
    rw [runFast_iterable_iterator hlist_jh2 harr_jh2]
    rw [runFast_astore]
    rw [hsz2]
    change Jvm.runJvmResFast _ (kFind + 3 + 24 * units.length) _ 30
      (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 30) ⟨30, [], locs3', jh3, hp⟩ = _
    rw [hMap]
    obtain ⟨kRem, hkRem⟩ := Nat.exists_eq_add_of_le' (by dsimp only [kFind]; omega : 12 ≤ kFind)
    rw [hkRem]
    dsimp only [PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog, List.drop]
    time_step_blk
    rw [hlEnd7]
    rw [runFast_checkcast_arrayList hEndList]
    time_step_blk
    rw [runFast_checkcast_arrayList hEndList]
    time_step_blk
    rw [runFast_iterable_iterator hEndList hEndArr']
    rw [runFast_astore]
    have hk_eq : kRem = kFind - 12 := by dsimp only [kFind]; omega
    rw [hk_eq]
    change Jvm.runJvmResFast _ (kFind - 12) _ 66 (PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog.drop 66)
      ⟨66, [], locs4, jh4, hp⟩ = _
    exact hFind
  exact ⟨endSt, hmod, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrun, hcEndSt, hhpEndSt⟩

end TimeUtil.KotlinJvmVerification

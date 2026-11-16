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

import MosaicSemantics
import proofs.KotlinJvmEquiv.CalculatorEngine
import proofs.KotlinJvmEquiv.CalculatorScreenCompose

namespace MosaicCalculator.KotlinJvmVerification

open MosaicCalculator.JvmVerification
open MosaicCalculator.KotlinJvmBytecode
open MosaicCalculator.Model

/-! ### Full Program Table & Helper Lemmas -/

theorem calcProgLookup_extends : ExtendsEngineProgs calcProgLookup := by
  intro fnTag prog h
  dsimp only [engineProgLookup] at h
  split at h <;> cases h <;> rfl

/-- Post-`<clinit>` static heap for `ComposableSingletons$CalculatorScreenKt` + `WhenMappings`. -/
def calcUiInitJvmHeap : Jvm.JvmHeap CalcExt :=
  ((((calcInitJvmHeap.setStatic "ComposableSingletons$CalculatorScreenKt" "INSTANCE"
      (.ext (.companion "ComposableSingletons$CalculatorScreenKt")))
    |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$125313259" (.ext (.closureRef 0)))
    |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$9509460" (.ext (.closureRef 1)))
    |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$2033009011" (.ext (.closureRef 2)))
    |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$-238458734" (.ext (.closureRef 3))

/-- Post-`<clinit>` singleton closure table for `ComposableSingletons$CalculatorScreenKt`. -/
def calcUiInitClosures : Array (String × List JvmVal) := #[
  ("ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0", []),
  ("ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0", []),
  ("ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0", []),
  ("ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0", [])
]

theorem calcUiInitJvmHeap_hasWhenMappings : HasCalcWhenMappings calcUiInitJvmHeap where
  opSwitch := ⟨0, rfl, rfl⟩
  errSwitch := ⟨1, rfl, rfl⟩
  staticsClean := by
    intro cls fld hne1 hne2
    have h1 : ("ComposableSingletons$CalculatorScreenKt" == cls) = false := beq_false_of_ne (Ne.symm hne2)
    have h2 : ("com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt$WhenMappings" == cls) = false :=
      beq_false_of_ne (Ne.symm hne1)
    simp [calcUiInitJvmHeap, calcInitJvmHeap, Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?,
      Jvm.JvmHeap.alloc, List.filter, h1, h2]

theorem calcUiInit_hasSingletonRowLambdas : HasSingletonRowLambdas calcUiInitJvmHeap calcUiInitClosures :=
  ⟨0, 1, 2, 3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private instance instHasDefaultIsZeroComposeUi (r : String → Option (List JvmInstr)) (d f : Nat) :
    Jvm.HasDefaultIsZero (mkCalcHooks r d f) where
  isZero?_eq := by cases d <;> rfl

local elab "unfold_ui_priv" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do
    let tgt ← g.getType
    let tgt' ← Lean.Meta.transform tgt fun e => do
      if let .const n _ := e.getAppFn then
        let s := n.toString
        if s.endsWith "isVoidStaticTarget" || s.endsWith "normalizeCalcClass" ||
           s.endsWith "singletonLambdaFnTag?" then
          if let some e' ← Lean.Meta.unfoldDefinition? e then
            return .done (← Lean.Meta.whnf e')
        else if s.contains "assignParamLocalsAux" || s.contains "assignLinearLocals" then
          let args := e.getAppArgs
          if let some lastArg := args.back? then
            let lastWhnf ← Lean.Meta.whnf lastArg
            if lastWhnf.isAppOf ``List.nil || lastWhnf.isAppOf ``List.cons then
              if let some e' ← Lean.Meta.unfoldDefinition? e then
                return .visit (← Lean.Meta.whnf e')
        else if s.contains "upsertGroup" || s.contains "findGroup?" ||
                s.contains "updateGroup" || s.contains "listSetAt" ||
                s.contains "recordReadInActiveGroups" then
          if s.endsWith ".match_1" then
            if let some e' ← Lean.Meta.unfoldDefinition? e then
              return .visit e'
          else
            let args := e.getAppArgs
            if args.any (fun a => a.isAppOf ``List.nil || a.isAppOf ``List.cons) then
              if let some e' ← Lean.Meta.unfoldDefinition? e then
                return .visit e'
      return .continue
    return [← g.replaceTargetDefEq tgt']

private theorem setLocal_same (locs : Nat → JvmVal) (idx : Nat) (v : JvmVal) :
    setLocal locs idx v idx = v := by
  dsimp only [setLocal]
  split
  · rfl
  · next h => exact False.elim (h rfl)

private theorem setLocal_diff (locs : Nat → JvmVal) {idx k : Nat} (v : JvmVal)
    (h : (k == idx) = false) : setLocal locs idx v k = locs k := by
  have hne : k ≠ idx := fun hc => by subst hc; simp at h
  dsimp only [setLocal]
  split
  · next hc => exact False.elim (hne hc)
  · rfl

local macro "peel_loc" : tactic =>
  `(tactic| repeat (first | rw [setLocal_same] | rw [setLocal_diff _ _ rfl]))

private theorem runFast_vreturn' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.vreturn :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      some (.unit, ⟨pc, stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .vreturn rest ⟨pc0, stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runFast_areturn' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [Jvm.runJvmResFast_step_nonbranch hooks f prog pc .areturn rest ⟨pc0, v :: stk, locs, jh, hp⟩ rfl (by simp)]
  rfl

private theorem runFast_goto' {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc pc0 target : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.goto target :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  rfl

private theorem runFast_ifnull_fallthrough' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnn : v.isNull = false) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifnull target :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hnn]

private theorem runFast_ifeq_zero [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hz : v = 0 := by decide) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifeq target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  subst hz
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks)]

private theorem runFast_ifeq_nonzero [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnz : v ≠ 0) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifeq target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks), hnz]

private theorem runFast_ifne_zero' [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hz : v = 0 := by decide) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  subst hz
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks)]

private theorem runFast_ifne_nonzero' [Jvm.HasDefaultIsZero hooks]
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hnz : v ≠ 0) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ifne target :: rest) ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch,
    Jvm.HasDefaultIsZero.isZero?_eq (hooks := hooks), hnz]

private theorem runFast_if_icmpeq_eq' {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (heq : a = b) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog target (prog.drop target) ⟨target, stk, locs, jh, hp⟩ := by
  subst heq
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch]

private theorem runFast_if_icmpeq_ne {hooks : Jvm.JvmHooks CalcExt CalcHeap}
    {f pc pc0 target : Nat} {prog rest : List JvmInstr} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (hne : a ≠ b) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.if_icmpeq target :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl)]
  simp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, hne]

private theorem runFast_if_acmpne_ext_branch {d subFuel f pc pc0 target : Nat}
    {prog rest : List JvmInstr} {a b : CalcExt} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hne : beqRefCalcExt a b = some false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.if_acmpne target :: rest) ⟨pc0, .ext b :: .ext a :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog target (prog.drop target)
        ⟨target, stk, locs, jh, hp⟩ := by
  rw [Jvm.runJvmResFast_at_branch_cons (mkCalcHooks calcProgLookup (d + 1) subFuel) (hbr := rfl)]
  dsimp only [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.refEq?]
  have hbeq : (mkCalcHooks calcProgLookup (d + 1) subFuel).beqRefExt = beqRefCalcExt := rfl
  rw [hbeq, hne]
  rfl

private theorem runFast_checkNotNull' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {param : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnn : v.isNull = false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc0, .str param :: v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V")
      ⟨pc, .str param :: v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric]
    simp [hnn]
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_isTraceInProgress' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} (ht : hp.composer.traceEnabled = false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩ := by
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z")
      ⟨pc, stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks]
    rw [ht]
    rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_shouldExecute' (d subFuel f pc pc0 : Nat)
    {prog rest : List JvmInstr} {p flags : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    let res := Compose.shouldExecute hp.composer (p != 0) flags.toInt32
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z" :: rest)
        ⟨pc0, .i32 flags :: .i32 p :: .ext .composer :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if res then 1 else 0) :: stk, locs, jh, hp⟩ := by
  intro res
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel)
      (.invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z")
      ⟨pc, .i32 flags :: .i32 p :: .ext .composer :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (if res then 1 else 0) :: stk, locs, jh, hp⟩) := rfl
  exact Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) rfl (by simp) hs rfl

private theorem runFast_getstatic_calcClean {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {cls fld desc : String} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hstep : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) subFuel) (.getstatic cls fld desc)
        ⟨pc, stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩)) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.getstatic cls fld desc :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, v :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) hstep rfl

private theorem runFast_getInitial {d subFuel f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "com/alexvanyo/composelife/mosaiccalculator/CalculatorState$Companion"
          "getInitial" "()Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" :: rest)
        ⟨pc, .ext (.companion "CalculatorState$Companion") :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcState .initial) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rfl

private theorem runFast_composerEmpty' {d subFuel f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokevirtual "androidx/compose/runtime/Composer$Companion" "getEmpty" "()Ljava/lang/Object;" :: rest)
        ⟨pc, .ext (.companion "Composer$Companion") :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext .composerEmpty :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rfl

private theorem runFast_invokedynamic_bsm1 {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {bsmArg desc fnTag : String} {c0 : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (htags : Jvm.parseMethodParamTags desc = ['L'])
    (hbsm : extractBsmTarget bsmArg = some fnTag) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg desc :: rest)
        ⟨pc, c0 :: stk, locs, jh, hp⟩ =
      let r := allocClosure hp fnTag [c0]
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef r.1) :: stk, locs, jh, r.2⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeDynamic _ _ _ _ = _
  dsimp only [mkCalcHooks]
  rw [show ("LambdaMetafactory" == "LambdaMetafactory") = true from rfl]
  simp only [↓reduceIte, htags, List.length_cons, List.length_nil]
  cases (stk.length + 1).decLt 1 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [hbsm]
    rfl

private theorem runFast_invokedynamic_bsm4 {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {bsmArg desc fnTag : String} {c0 c1 c2 c3 : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (htags : Jvm.parseMethodParamTags desc = ['L', 'L', 'I', 'I'])
    (hbsm : extractBsmTarget bsmArg = some fnTag) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg desc :: rest)
        ⟨pc, c3 :: c2 :: c1 :: c0 :: stk, locs, jh, hp⟩ =
      let r := allocClosure hp fnTag [c0, c1, c2, c3]
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef r.1) :: stk, locs, jh, r.2⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeDynamic _ _ _ _ = _
  dsimp only [mkCalcHooks]
  rw [show ("LambdaMetafactory" == "LambdaMetafactory") = true from rfl]
  simp only [↓reduceIte, htags, List.length_cons, List.length_nil]
  cases (stk.length + 4).decLt 4 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [hbsm]
    rfl

private theorem parseTags_app_bsm30 :
    Jvm.parseMethodParamTags "(Landroidx/compose/runtime/MutableState;)Lkotlin/jvm/functions/Function1;" =
      ['L'] := by
  decide

set_option maxRecDepth 2048 in
private theorem parseTags_app_bsm4 :
    Jvm.parseMethodParamTags
      "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/modifier/Modifier;II)Lkotlin/jvm/functions/Function2;" =
      ['L', 'L', 'I', 'I'] := by
  decide

private theorem traceEnabled_startRestart (m : Compose.ComposerModel JvmVal) (k : Int32) :
    (Compose.startRestartGroup m k).traceEnabled = m.traceEnabled := rfl

private theorem traceEnabled_startDefaults (m : Compose.ComposerModel JvmVal) :
    (Compose.startDefaults m).traceEnabled = m.traceEnabled := by
  dsimp only [Compose.startDefaults]
  cases m.groupStack <;> rfl

private theorem traceEnabled_skipToGroupEnd (m : Compose.ComposerModel JvmVal) :
    (Compose.skipToGroupEnd m).traceEnabled = m.traceEnabled := by
  dsimp only [Compose.skipToGroupEnd]
  cases m.groupStack with
  | nil => rfl
  | cons f _ => dsimp only; cases f.inDefaults <;> rfl

private theorem traceEnabled_endDefaults (m : Compose.ComposerModel JvmVal) :
    (Compose.endDefaults m).traceEnabled = m.traceEnabled := by
  dsimp only [Compose.endDefaults]
  cases m.groupStack <;> rfl

private theorem traceEnabled_allocMutable (m : Compose.ComposerModel JvmVal) (v : JvmVal) :
    (Compose.allocMutableState m v).2.traceEnabled = m.traceEnabled := rfl

private theorem traceEnabled_readRemember (m : Compose.ComposerModel JvmVal) :
    (Compose.readRememberSlot m).2.traceEnabled = m.traceEnabled := by
  dsimp only [Compose.readRememberSlot]
  cases m.groupStack with
  | nil => rfl
  | cons _ _ => dsimp only; split <;> rfl

private theorem traceEnabled_writeRemember (m : Compose.ComposerModel JvmVal) (v : JvmVal) :
    (Compose.writeRememberSlot m v).traceEnabled = m.traceEnabled := by
  dsimp only [Compose.writeRememberSlot]
  cases m.groupStack with
  | nil => rfl
  | cons _ _ => dsimp only; split <;> rfl

private theorem traceEnabled_endRestartGroup (m : Compose.ComposerModel JvmVal) :
    (Compose.endRestartGroup m).2.traceEnabled = m.traceEnabled := by
  dsimp only [Compose.endRestartGroup]
  cases m.groupStack <;> rfl

private theorem traceEnabled_setGroupRestartClosure (m : Compose.ComposerModel JvmVal)
    (k : Int32) (c : JvmVal) :
    (Compose.setGroupRestartClosure m k c).traceEnabled = m.traceEnabled := rfl

private theorem updateChangedFlags_one : Compose.updateChangedFlags 1 = 1 := by
  decide

/-! ### `CalculatorApp$lambda$1`, `$lambda$2`, `$lambda$3$0` -/

private theorem CalculatorApp_lambda_1_equiv_fuel (d subFuel fuel : Nat)
    (hd : 1 ≤ d) (hf : 20 ≤ fuel) (sid : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) (cSt : CalculatorState)
    (comp' : Compose.ComposerModel JvmVal)
    (hread : Compose.readMutableState hp.composer sid = some (.ext (.calcState cSt), comp')) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_1_prog
          (initCalcJvmState [(0, .ext (.stateRef sid))] hp jh) =
        some (.ext (.calcState cSt), st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  let hooks := mkCalcHooks calcProgLookup (d' + 1) subFuel
  let locs0 : Nat → JvmVal := setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid))
  have hl0 : locs0 0 = .ext (.stateRef sid) := rfl
  have hFast : ∃ st' : JvmState,
      Jvm.runJvmResFast hooks (kF + 20) CalculatorApp_lambda_1_prog 0 CalculatorApp_lambda_1_prog
          ⟨0, [], locs0, jh, hp⟩ =
        some (.ext (.calcState cSt), st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
    dsimp only [CalculatorApp_lambda_1_prog]
    rw [runFast_aload, hl0]
    have hcc1 : Jvm.stepInstr hooks (.checkcast "androidx/compose/runtime/State")
        ⟨1, [.ext (.stateRef sid)], locs0, jh, hp⟩ =
        .inl (some ⟨2, [.ext (.stateRef sid)], locs0, jh, hp⟩) := rfl
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hcc1 rfl]
    rw [runFast_astore, runFast_aconstNull, runFast_astore, runFast_aconstNull, runFast_astore,
      runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    have hget : Jvm.stepInstr hooks
        (.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;")
        ⟨10, [.ext (.stateRef sid)],
          (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
          jh, hp⟩ =
        .inl (some ⟨11, [.ext (.calcState cSt)],
          (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
          jh, { hp with composer := comp' }⟩) := by
      have hgen : Jvm.stepInstr hooks
          (.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;")
          ⟨10, [.ext (.stateRef sid)],
            (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
            jh, hp⟩ =
          match Compose.readMutableState hp.composer sid with
          | some (v, comp'') => .inl (some ⟨11, [v],
              (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
              jh, { hp with composer := comp'' }⟩)
          | none => .inr none := rfl
      rw [hgen, hread]
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hget rfl]
    have hcc2 : Jvm.stepInstr hooks (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorState")
        ⟨11, [.ext (.calcState cSt)],
          (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
          jh, { hp with composer := comp' }⟩ =
        .inl (some ⟨12, [.ext (.calcState cSt)],
          (setLocal (setLocal (setLocal (setLocal locs0 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)),
          jh, { hp with composer := comp' }⟩) := rfl
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hcc2 rfl]
    rw [runFast_areturn']
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨st', hrun, hjh', hhp'⟩ := hFast
  exact ⟨st', Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrun, hjh', hhp'⟩

private theorem CalculatorApp_lambda_2_equiv_fuel (d subFuel fuel : Nat)
    (hd : 1 ≤ d) (hf : 20 ≤ fuel) (sid : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) (cSt : CalculatorState)
    (comp' : Compose.ComposerModel JvmVal)
    (hwrite : Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt)
      hp.composer sid (.ext (.calcState cSt)) = some comp') :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_2_prog
          (initCalcJvmState [(0, .ext (.stateRef sid)), (1, .ext (.calcState cSt))] hp jh) =
        some (.unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  let hooks := mkCalcHooks calcProgLookup (d' + 1) subFuel
  let locs0 : Nat → JvmVal :=
    setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid))) 1 (.ext (.calcState cSt))
  have hl0 : locs0 0 = .ext (.stateRef sid) := rfl
  have hl1 : locs0 1 = .ext (.calcState cSt) := rfl
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  have hFast : ∃ st' : JvmState,
      Jvm.runJvmResFast hooks (kF + 20) CalculatorApp_lambda_2_prog 0 CalculatorApp_lambda_2_prog
          ⟨0, [], locs0, jh, hp⟩ =
        some (.unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
    dsimp only [CalculatorApp_lambda_2_prog]
    rw [runFast_aload, hl0, runFast_astore, runFast_aconstNull, runFast_astore, runFast_aconstNull,
      runFast_astore, runFast_aload]; peel_loc; rw [hl1, runFast_astore, runFast_iconst, runFast_istore,
      runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc
    have hset : Jvm.stepInstr hooks
        (.invokeinterface "androidx/compose/runtime/MutableState" "setValue" "(Ljava/lang/Object;)V")
        ⟨12, [.ext (.calcState cSt), .ext (.stateRef sid)],
          setLocal (setLocal (setLocal (setLocal (setLocal locs0 2 (.ext (.stateRef sid))) 3 .null) 4 .null)
            5 (.ext (.calcState cSt))) 6 (.i32 0), jh, hp⟩ =
        .inl (some ⟨13, [],
          setLocal (setLocal (setLocal (setLocal (setLocal locs0 2 (.ext (.stateRef sid))) 3 .null) 4 .null)
            5 (.ext (.calcState cSt))) 6 (.i32 0), jh, { hp with composer := comp' }⟩) := by
      have hgen : Jvm.stepInstr hooks
          (.invokeinterface "androidx/compose/runtime/MutableState" "setValue" "(Ljava/lang/Object;)V")
          ⟨12, [.ext (.calcState cSt), .ext (.stateRef sid)],
            setLocal (setLocal (setLocal (setLocal (setLocal locs0 2 (.ext (.stateRef sid))) 3 .null) 4 .null)
              5 (.ext (.calcState cSt))) 6 (.i32 0), jh, hp⟩ =
          match Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt)
              hp.composer sid (.ext (.calcState cSt)) with
          | some comp'' => .inl (some ⟨13, [],
              setLocal (setLocal (setLocal (setLocal (setLocal locs0 2 (.ext (.stateRef sid))) 3 .null) 4 .null)
                5 (.ext (.calcState cSt))) 6 (.i32 0), jh, { hp with composer := comp'' }⟩)
          | none => .inr none := rfl
      rw [hgen, hwrite]
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hset rfl]
    rw [runFast_nop, runFast_vreturn']
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨st', hrun, hjh', hhp'⟩ := hFast
  exact ⟨st', Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrun, hjh', hhp'⟩

set_option maxRecDepth 4096 in
/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorApp$lambda$3$0` (`onKey`). -/
theorem CalculatorApp_lambda_3_0_equiv (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 80 ≤ subFuel) (hf : 20 ≤ fuel)
    (sid : Nat) (k : CalculatorKey) (cSt : CalculatorState)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) (hw : HasCalcWhenMappings jh)
    (comp1 comp2 : Compose.ComposerModel JvmVal)
    (hread : Compose.readMutableState hp.composer sid = some (.ext (.calcState cSt), comp1))
    (hwrite : Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt) comp1 sid
      (.ext (.calcState (reduceCalculatorStateModel cSt k))) = some comp2) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_3_0_prog
          (initCalcJvmState [(0, .ext (.stateRef sid)), (1, .ext (.calcKey k))] hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with composer := comp2 } := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hlam1 := CalculatorApp_lambda_1_equiv_fuel (d' + 3) subFuel subFuel (by omega)
    (by omega) sid hp jh cSt comp1 hread
  let hp1 : CalcHeap := { hp with composer := comp1 }
  have hred := reduceCalculatorState_equiv calcProgLookup calcProgLookup_extends (d' + 3) subFuel subFuel
    (by omega) (by omega) (by omega) cSt k hp1 jh hw
  let newSt := reduceCalculatorStateModel cSt k
  have hlam2 := CalculatorApp_lambda_2_equiv_fuel (d' + 3) subFuel subFuel (by omega)
    (by omega) sid hp1 jh newSt comp2 hwrite
  obtain ⟨st1, hrun1, hjh1, hhp1⟩ := hlam1
  obtain ⟨stR, hrunR, hjhR, hhpR⟩ := hred
  obtain ⟨st2, hrun2, hjh2, hhp2⟩ := hlam2
  let locs0 : Nat → JvmVal :=
    setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid))) 1 (.ext (.calcKey k))
  have hl0 : locs0 0 = .ext (.stateRef sid) := rfl
  have hl1 : locs0 1 = .ext (.calcKey k) := rfl
  have hst1Step : ∀ {f0 pc0 : Nat} {prog0 rest0 : List JvmInstr} {stk0 : List JvmVal}
      {locs : Nat → JvmVal},
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (f0 + 1) prog0 pc0
          (.invokestatic "CalculatorScreenKt" "CalculatorApp$lambda$1"
            "(Landroidx/compose/runtime/MutableState;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" ::
            rest0)
          ⟨pc0, .ext (.stateRef sid) :: stk0, locs, jh, hp⟩ =
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) f0 prog0 (pc0 + 1) rest0
          ⟨pc0 + 1, .ext (.calcState cSt) :: stk0, locs, jh, hp1⟩ := by
    intro f0 pc0 prog0 rest0 stk0 locs
    refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
    change (mkCalcHooks calcProgLookup (d' + 4) subFuel).stepInvokeStatic _ _ _ _ = _
    conv => lhs; whnf
    unfold_ui_priv
    dsimp only
    rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorApp$lambda$1" =
      "CalculatorScreenKt.CalculatorApp$lambda$1" from by apply String.ext; simp]
    rw [show Jvm.parseMethodParamTags
        "(Landroidx/compose/runtime/MutableState;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" =
        ['L'] from by decide]
    dsimp only [List.length]
    cases (stk0.length + 1).decLt 1 with
    | isTrue h => omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$1" =
        some CalculatorApp_lambda_1_prog from rfl]
      unfold_ui_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun1 ⊢
      rw [hrun1]
      dsimp only
      rw [hjh1, hhp1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
  have hredStep : ∀ {f0 pc0 : Nat} {prog0 rest0 : List JvmInstr} {stk0 : List JvmVal}
      {locs : Nat → JvmVal},
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (f0 + 1) prog0 pc0
          (.invokestatic "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt"
            "reduceCalculatorState"
            "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" ::
            rest0)
          ⟨pc0, .ext (.calcKey k) :: .ext (.calcState cSt) :: stk0, locs, jh, hp1⟩ =
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) f0 prog0 (pc0 + 1) rest0
          ⟨pc0 + 1, .ext (.calcState newSt) :: stk0, locs, jh, hp1⟩ := by
    intro f0 pc0 prog0 rest0 stk0 locs
    refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
    change (mkCalcHooks calcProgLookup (d' + 4) subFuel).stepInvokeStatic _ _ _ _ = _
    conv => lhs; whnf
    unfold_ui_priv
    dsimp only
    rw [show "CalculatorEngineKt" ++ "." ++ "reduceCalculatorState" =
      "CalculatorEngineKt.reduceCalculatorState" from by apply String.ext; simp]
    rw [show Jvm.parseMethodParamTags
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" =
        ['L', 'L'] from by decide]
    dsimp only [List.length]
    cases (stk0.length + 2).decLt 2 with
    | isTrue h => omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      rw [show calcProgLookup "CalculatorEngineKt.reduceCalculatorState" =
        some reduceCalculatorState_prog from rfl]
      unfold_ui_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrunR ⊢
      rw [hrunR]
      dsimp only
      rw [hjhR, hhpR]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
  have hlam2Step : ∀ {f0 pc0 : Nat} {prog0 rest0 : List JvmInstr} {stk0 : List JvmVal}
      {locs : Nat → JvmVal},
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (f0 + 1) prog0 pc0
          (.invokestatic "CalculatorScreenKt" "CalculatorApp$lambda$2"
            "(Landroidx/compose/runtime/MutableState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)V" ::
            rest0)
          ⟨pc0, .ext (.calcState newSt) :: .ext (.stateRef sid) :: stk0, locs, jh, hp1⟩ =
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) f0 prog0 (pc0 + 1) rest0
          ⟨pc0 + 1, stk0, locs, jh, { hp with composer := comp2 }⟩ := by
    intro f0 pc0 prog0 rest0 stk0 locs
    refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
    change (mkCalcHooks calcProgLookup (d' + 4) subFuel).stepInvokeStatic _ _ _ _ = _
    conv => lhs; whnf
    unfold_ui_priv
    dsimp only
    rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorApp$lambda$2" =
      "CalculatorScreenKt.CalculatorApp$lambda$2" from by apply String.ext; simp]
    rw [show Jvm.parseMethodParamTags
        "(Landroidx/compose/runtime/MutableState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;)V" =
        ['L', 'L'] from by decide]
    dsimp only [List.length]
    cases (stk0.length + 2).decLt 2 with
    | isTrue h => omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$2" =
        some CalculatorApp_lambda_2_prog from rfl]
      unfold_ui_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun2 ⊢
      rw [hrun2]
      dsimp only
      rw [hjh2, hhp2]
      simp only [↓reduceIte]
      rfl
  have hunitClean : jh.getStatic? "kotlin/Unit" "INSTANCE" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl]
  have hFast : ∃ endSt : JvmState,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (kF + 20)
          CalculatorApp_lambda_3_0_prog 0 CalculatorApp_lambda_3_0_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = { hp with composer := comp2 } := by
    dsimp only [CalculatorApp_lambda_3_0_prog]
    rw [runFast_aload, hl1, runFast_ldcStr]
    rw [runFast_checkNotNull' (d' + 3) subFuel _ _ _ rfl]
    rw [runFast_aload, hl0, runFast_aload, hl0, hst1Step, runFast_aload, hl1, hredStep, hlam2Step]
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hunitClean]; rfl)]
    rw [runFast_areturn']
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨endSt, hrunFast, hjh', hhp'⟩ := hFast
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrunFast, hjh', hhp'⟩

/-! ### `CalculatorApp` Cast & Call Helpers -/

private theorem checkCast_mutableState {d subFuel f pc : Nat} {prog rest : List JvmInstr}
    {sid : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "androidx/compose/runtime/MutableState" :: rest)
        ⟨pc, .ext (.stateRef sid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.stateRef sid) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rfl

private theorem checkCast_modifier {d subFuel f pc : Nat} {prog rest : List JvmInstr}
    {h? : Option Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "com/jakewharton/mosaic/modifier/Modifier" :: rest)
        ⟨pc, .ext (.modifier h?) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.modifier h?) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rfl

private theorem checkCast_function1 {d subFuel f pc : Nat} {prog rest : List JvmInstr}
    {cid : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.checkcast "kotlin/jvm/functions/Function1" :: rest)
        ⟨pc, .ext (.closureRef cid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cid) :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  rfl

private theorem invoke_CalculatorApp_lambda_1_step {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {sid : Nat} {cSt : CalculatorState}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} {hpEnd : CalcHeap}
    (hsub : ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) subFuel CalculatorApp_lambda_1_prog
          (initCalcJvmState [(0, .ext (.stateRef sid))] hp jh) =
        some (.ext (.calcState cSt), st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hpEnd) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "CalculatorScreenKt" "CalculatorApp$lambda$1"
          "(Landroidx/compose/runtime/MutableState;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" ::
          rest)
        ⟨pc, .ext (.stateRef sid) :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, .ext (.calcState cSt) :: stk, locs, jh, hpEnd⟩ := by
  obtain ⟨st', hrun, hjh, hhp⟩ := hsub
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeStatic _ _ _ _ = _
  conv => lhs; whnf
  unfold_ui_priv
  dsimp only
  rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorApp$lambda$1" =
    "CalculatorScreenKt.CalculatorApp$lambda$1" from by apply String.ext; simp]
  rw [show Jvm.parseMethodParamTags
      "(Landroidx/compose/runtime/MutableState;)Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;" =
      ['L'] from by decide]
  dsimp only [List.length]
  cases (stk.length + 1).decLt 1 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$1" =
      some CalculatorApp_lambda_1_prog from rfl]
    unfold_ui_priv
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
    rw [hrun]
    dsimp only
    rw [hjh, hhp]
    simp only [Bool.false_eq_true, ↓reduceIte]

set_option maxRecDepth 4096 in
private theorem invoke_CalculatorScreen_step {d subFuel f pc : Nat}
    {prog rest : List JvmInstr} {cSt : CalculatorState} {onKey modV : JvmVal}
    {ch defF : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} {hpEnd : CalcHeap}
    (hsub : ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) subFuel CalculatorScreen_prog
          (initCalcJvmState
            [(0, .ext (.calcState cSt)), (1, onKey), (2, modV), (3, .ext .composer),
             (4, .i32 ch), (5, .i32 defF)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = hpEnd) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) (f + 1) prog pc
        (.invokestatic "CalculatorScreenKt" "CalculatorScreen"
          "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" ::
          rest)
        ⟨pc, .i32 defF :: .i32 ch :: .ext .composer :: modV :: onKey :: .ext (.calcState cSt) :: stk,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) subFuel) f prog (pc + 1) rest
        ⟨pc + 1, stk, locs, jh, hpEnd⟩ := by
  obtain ⟨endSt, hrun, hjh, hhp⟩ := hsub
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  change (mkCalcHooks calcProgLookup (d + 1) subFuel).stepInvokeStatic _ _ _ _ = _
  conv => lhs; whnf
  unfold_ui_priv
  dsimp only
  rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorScreen" = "CalculatorScreenKt.CalculatorScreen"
    from by apply String.ext; simp]
  rw [show Jvm.parseMethodParamTags
      "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" =
      ['L', 'L', 'L', 'L', 'I', 'I'] from by decide]
  dsimp only [List.length]
  cases (stk.length + 6).decLt 6 with
  | isTrue h => omega
  | isFalse _ =>
    dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
    rw [show calcProgLookup "CalculatorScreenKt.CalculatorScreen" = some CalculatorScreen_prog from rfl]
    unfold_ui_priv
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrun ⊢
    rw [hrun]
    dsimp only
    rw [hjh, hhp]
    simp only [↓reduceIte]

/-! ### `CalculatorApp` Initial & Recomposition Proofs -/

/-- Core initial composition equivalence for `CalculatorApp(ch = 0, defF = 3)`. -/
theorem CalculatorApp_initial_equiv (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 150 ≤ subFuel) (hf : 200 ≤ fuel)
    (initArg modArg : JvmVal)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hcomp : hp.composer = {})
    (hns : hp.nodeStack = [])
    (hw : HasCalcWhenMappings jh)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    let cidOnKey := hp.closures.size
    let cidKey := cidOnKey + 1
    let cidCol := cidKey + 1
    let cidScrRestart := cidCol + 1
    let cidAppRestart := cidScrRestart + 1
    let closuresEnd :=
      ((((hp.closures.push ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]))
        |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [.ext (.closureRef cidOnKey)]))
        |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState .initial)]))
        |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState .initial), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
        |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState .initial), .ext (.modifier none), .i32 0, .i32 3])
    ∃ endSt gApp gScr,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_prog
          (initCalcJvmState [(0, initArg), (1, modArg), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode .initial cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState .initial))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp, gScr] ∧
      gApp.key = (54337357 : Int32) ∧
      gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr.key = (2094116101 : Int32) ∧
      gScr.slots = [.ext (.calcState .initial), .ext (.closureRef cidKey)] ∧
      gScr.dirty = false ∧
      gScr.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hcompStatic : jh.getStatic? "androidx/compose/runtime/Composer" "Companion" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  have hcalcCompStatic :
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "Companion" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  have hmodStatic :
      jh.getStatic? "com/jakewharton/mosaic/modifier/Modifier" "Companion" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  have hstableStatic :
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "$stable" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  let c0 := Compose.startRestartGroup hp.composer 54337357
  let c1 := Compose.startDefaults c0
  let c2 := Compose.endDefaults c1
  let c3 := (Compose.readRememberSlot c2).2
  let c4 := (Compose.allocMutableState c3 (.ext (.calcState .initial))).2
  let sid := (Compose.allocMutableState c3 (.ext (.calcState .initial))).1
  let c5 := Compose.writeRememberSlot c4 (.ext (.stateRef sid))
  have hsid : sid = 0 := by dsimp only [sid, c4, c3, c2, c1, c0]; rw [hcomp]; rfl
  have hc0Ins : c0.inserting = true := by dsimp only [c0]; rw [hcomp]; rfl
  have hc2Trace : c2.traceEnabled = false := by dsimp only [c2, c1, c0]; rw [hcomp]; rfl
  have hc3Empty : (Compose.readRememberSlot c2).1 = none := by
    dsimp only [c2, c1, c0]; rw [hcomp]; rfl
  let cidOnKey := hp.closures.size
  let c5r : Compose.ComposerModel JvmVal := {
    inserting := true
    groups := [{ key := 54337357, slots := [.ext (.stateRef 0)], dirty := false, reads := [0], restartClosure? := none }]
    groupStack := [{ key := 54337357, cursor := 1, lastReadIdx? := none, inDefaults := false, skipped := false }]
    stateCells := [(0, .ext (.calcState .initial))]
    nextStateId := 1
    traceEnabled := false
  }
  have hc5Read : Compose.readMutableState c5 sid = some (.ext (.calcState .initial), c5r) := by
    dsimp only [c5r, sid, c5, c4, c3, c2, c1, c0]
    rw [hcomp]
    unfold_ui_priv
    rfl
  let c6 := (Compose.readRememberSlot c5r).2
  let c7 := Compose.writeRememberSlot c6 (.ext (.closureRef cidOnKey))
  have hlam1 := CalculatorApp_lambda_1_equiv_fuel (d' + 3) subFuel subFuel (by omega)
    (by omega) sid { hp with composer := c5 } jh .initial c5r hc5Read
  have hc5Empty : (Compose.readRememberSlot c5r).1 = none := by
    dsimp only [c5r]
    rfl
  let hpPreScr : CalcHeap := {
    hp with
    composer := c7
    closures := hp.closures.push ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef sid)])
  }
  have htrPreScr : hpPreScr.composer.traceEnabled = false := by
    dsimp only [hpPreScr, c7, c6, c5r]
    rfl
  have hGroupsPre : ∃ gApp0, hpPreScr.composer.groups = [gApp0] ∧ gApp0.key = (54337357 : Int32) :=
    ⟨{ key := 54337357, slots := [.ext (.stateRef 0), .ext (.closureRef cidOnKey)], dirty := false,
        reads := [0], restartClosure? := none },
      rfl, rfl⟩
  have hsingPre : HasSingletonRowLambdas jh hpPreScr.closures := by
    obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hsing
    have hlt0 : id0 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc0).1
    have hlt1 : id1 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc1).1
    have hlt2 : id2 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc2).1
    have hlt3 : id3 < hp.closures.size := (Array.getElem?_eq_some_iff.mp hc3).1
    refine ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, ?_, ?_, ?_, ?_⟩
    · dsimp only [hpPreScr]
      rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hlt0, ← Array.getElem?_eq_getElem hlt0]
      exact hc0
    · dsimp only [hpPreScr]
      rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hlt1, ← Array.getElem?_eq_getElem hlt1]
      exact hc1
    · dsimp only [hpPreScr]
      rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hlt2, ← Array.getElem?_eq_getElem hlt2]
      exact hc2
    · dsimp only [hpPreScr]
      rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hlt3, ← Array.getElem?_eq_getElem hlt3]
      exact hc3
  have hscr := CalculatorScreen_initial_equiv (d' + 3) subFuel subFuel (by omega) (by omega)
    (by omega) .initial (.ext (.closureRef cidOnKey)) rfl hpPreScr jh htrPreScr
    (.inr hGroupsPre) hw.errSwitch hw.staticsClean hsingPre
  obtain ⟨stScr, hrunScr, hjhScr, hhpScr⟩ := hscr
  let cidKey := cidOnKey + 1
  let cidCol := cidKey + 1
  let cidScrRestart := cidCol + 1
  let cidAppRestart := cidScrRestart + 1
  let sr1 := Compose.startRestartGroup hpPreScr.composer 2094116101
  let sr2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) sr1 (.ext (.calcState .initial))).2
  let sr3 := (Compose.readRememberSlot sr2).2
  let sr4 := Compose.writeRememberSlot sr3 (.ext (.closureRef cidKey))
  let sr5 := (Compose.endRestartGroup sr4).2
  let compScrEnd := Compose.setGroupRestartClosure sr5 2094116101 (.ext (.closureRef cidScrRestart))
  let hpScrEnd : CalcHeap := {
    emitMosaicNode { hpPreScr with
      composer := sr4
      closures := (hpPreScr.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0",
        [.ext (.closureRef cidOnKey)])).push ("CalculatorScreenKt.CalculatorScreen$lambda$1",
          [.ext (.calcState .initial)]) }
      (calculatorScreenMosaicNode .initial cidKey) with
    composer := compScrEnd
    closures := ((hpPreScr.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0",
      [.ext (.closureRef cidOnKey)])).push ("CalculatorScreenKt.CalculatorScreen$lambda$1",
        [.ext (.calcState .initial)])).push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState .initial), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0])
  }
  have hhpScr' : stScr.heap = hpScrEnd := by
    rw [hhpScr]
    dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, cidScrRestart, cidCol, cidKey, hpPreScr, cidOnKey]
    simp only [Array.size_push]
  have hscrRun' : Jvm.runJvmRes (mkCalcHooks calcProgLookup (d' + 3) subFuel) subFuel CalculatorScreen_prog
      (initCalcJvmState
        [(0, .ext (.calcState .initial)), (1, .ext (.closureRef cidOnKey)), (2, .ext (.modifier none)),
         (3, .ext .composer), (4, .i32 432), (5, .i32 0)]
        hpPreScr jh) =
      some (.unit, stScr) ∧ stScr.jvmHeap = jh ∧ stScr.heap = hpScrEnd :=
    ⟨hrunScr, hjhScr, hhpScr'⟩
  have htrScrEnd : hpScrEnd.composer.traceEnabled = false := by
    dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]
    rfl
  have hEndKey : (Compose.endRestartGroup hpScrEnd.composer).1 = some 54337357 := by
    dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]
    rfl
  have hnsEnd : hpScrEnd.nodeStack = [] := by
    dsimp only [hpScrEnd, emitMosaicNode, hpPreScr]; rw [hns]
  have hrootEnd : hpScrEnd.emittedRoot? = some (calculatorScreenMosaicNode .initial cidKey) := by
    dsimp only [hpScrEnd, emitMosaicNode, hpPreScr]; rw [hns]
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt (fun _ => .i32 0) 0 initArg)
            1 modArg)
          2 (.ext .composer))
        3 (.i32 0))
      4 (.i32 3)
  have hl0 : locs0 0 = initArg := rfl
  have hl1 : locs0 1 = modArg := rfl
  have hl2 : locs0 2 = .ext .composer := rfl
  have hl3 : locs0 3 = .i32 0 := rfl
  have hl4 : locs0 4 = .i32 3 := rfl
  have hFast :
      ∃ (endSt : JvmState) (gApp gScr : Compose.GroupEntry JvmVal),
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (kF + 200)
            CalculatorApp_prog 0 CalculatorApp_prog ⟨0, [], locs0, jh, hp⟩ =
          some (.unit, endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.closures =
          (((((hp.closures.push ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]))
            |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [.ext (.closureRef cidOnKey)]))
            |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState .initial)]))
            |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
              [.ext (.calcState .initial), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
            |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
              [.ext (.calcState .initial), .ext (.modifier none), .i32 0, .i32 3])) ∧
        endSt.heap.nodeStack = [] ∧
        endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode .initial cidKey) ∧
        endSt.heap.composer.traceEnabled = false ∧
        endSt.heap.composer.groupStack = [] ∧
        endSt.heap.composer.stateCells = [(0, .ext (.calcState .initial))] ∧
        endSt.heap.composer.nextStateId = 1 ∧
        endSt.heap.composer.groups = [gApp, gScr] ∧
        gApp.key = (54337357 : Int32) ∧
        gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
        gApp.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
        gScr.key = (2094116101 : Int32) ∧
        gScr.slots = [.ext (.calcState .initial), .ext (.closureRef cidKey)] ∧
        gScr.dirty = false ∧
        gScr.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
    dsimp only [CalculatorApp_prog]
    rw [runFast_aload, hl2, runFast_iconst, runFast_startRestartGroup, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_ldcStr, runFast_sourceInfo]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_iconst, runFast_iand, runFast_ifne_zero']
    rw [runFast_iload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand]
    rw [runFast_ifne_nonzero' (by decide)]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_iconst, runFast_ior, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_ior, runFast_istore, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
    rw [runFast_if_icmpeq_eq' (by decide)]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_iconst, runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_shouldExecute']
    dsimp only
    rw [show Compose.startRestartGroup hp.composer (UInt32.toInt32 54337357) = c0 from rfl]
    simp only [Compose.shouldExecute, hc0Ins, Bool.true_or, ↓reduceIte]
    rw [runFast_ifeq_nonzero (by decide)]
    rw [runFast_aload]; peel_loc; rw [runFast_startDefaults]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_iconst, runFast_iand, runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hcalcCompStatic]; rfl),
      runFast_getInitial, runFast_astore]
    rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hmodStatic]; rfl),
      checkCast_modifier, runFast_astore, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_endDefaults]
    rw [show Compose.endDefaults (Compose.startDefaults c0) = c2 from rfl]
    rw [runFast_isTraceInProgress' (d' + 3) subFuel _ _ _ (hp := { hp with composer := c2 }) hc2Trace,
      runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_iconst, runFast_istore, runFast_iconst, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
    dsimp only
    rw [hc3Empty]
    dsimp only [Option.getD]
    rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hcompStatic]; rfl),
      runFast_composerEmpty']
    rw [runFast_if_acmpne_ext rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_aconstNull, runFast_iconst, runFast_aconstNull, runFast_mutableStateOfDefault]
    dsimp only
    rw [runFast_astore, runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [runFast_updateRememberedValue]
    rw [runFast_aload]; peel_loc; rw [runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_nop, runFast_nop, checkCast_mutableState, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_sourceInfoMarkerEnd]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_aload]; peel_loc
    rw [show Compose.writeRememberSlot (Compose.allocMutableState c3 (.ext (.calcState .initial))).2
        (.ext (.stateRef (Compose.allocMutableState c3 (.ext (.calcState .initial))).1)) = c5 from rfl]
    rw [show (Compose.allocMutableState c3 (.ext (.calcState .initial))).1 = sid from rfl]
    rw [invoke_CalculatorApp_lambda_1_step hlam1]
    rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_iconst, runFast_istore, runFast_iconst, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
    dsimp only
    rw [hc5Empty]
    dsimp only [Option.getD]
    rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hcompStatic]; rfl),
      runFast_composerEmpty']
    rw [runFast_if_acmpne_ext rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_invokedynamic_bsm1 parseTags_app_bsm30 bsm_CalculatorApp_lambda_3_0]
    dsimp only [allocClosure]
    rw [runFast_aload]; peel_loc; rw [runFast_swap, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [runFast_updateRememberedValue]
    rw [runFast_aload]; peel_loc; rw [runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_nop, runFast_nop, checkCast_function1, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_sourceInfoMarkerEnd]
    rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc
    rw [runFast_iconst,
      runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hstableStatic]; rfl),
      runFast_ior]
    rw [runFast_iconst, runFast_iload]; peel_loc; rw [runFast_iconst, runFast_ishl, runFast_iand, runFast_ior]
    rw [runFast_iconst]
    rw [show (48 : UInt32) ||| (0 : UInt32) ||| (896 : UInt32) &&&
        (((0 : UInt32) ||| (2 : UInt32) ||| (48 : UInt32)) &&& (4294967281 : UInt32)) <<<
          ((3 : UInt32) &&& (31 : UInt32)) = (432 : UInt32) from by decide]
    rw [show ({
      hp with
      composer := Compose.writeRememberSlot c6 (.ext (.closureRef cidOnKey))
      closures := hp.closures.push ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef sid)])
    } : CalcHeap) = hpPreScr from rfl]
    rw [invoke_CalculatorScreen_step ⟨stScr, hscrRun'⟩]
    rw [runFast_isTraceInProgress' (d' + 3) subFuel _ _ _ htrScrEnd, runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_endRestartGroup]
    dsimp only
    rw [hEndKey]
    dsimp only
    rw [runFast_dup, runFast_ifnull_fallthrough' rfl]
    rw [runFast_aload]; peel_loc; rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl3]
    rw [runFast_iload]; peel_loc; rw [hl4]
    rw [runFast_invokedynamic_bsm4 parseTags_app_bsm4 bsm_CalculatorApp_lambda_4]
    dsimp only [allocClosure]
    rw [runFast_updateScope, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_vreturn']
    let gAppEnd : Compose.GroupEntry JvmVal := {
      key := (54337357 : Int32)
      slots := [.ext (.stateRef 0), .ext (.closureRef cidOnKey)]
      dirty := false
      reads := [0]
      restartClosure? := some (.ext (.closureRef cidAppRestart))
    }
    let gScrEnd : Compose.GroupEntry JvmVal := {
      key := (2094116101 : Int32)
      slots := [.ext (.calcState .initial), .ext (.closureRef cidKey)]
      dirty := false
      reads := []
      restartClosure? := some (.ext (.closureRef cidScrRestart))
    }
    refine ⟨_, gAppEnd, gScrEnd, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only [hpScrEnd, hpPreScr]; simp [hsid]
    · dsimp only [hpScrEnd, emitMosaicNode, hpPreScr]; rw [hns]
    · dsimp only [hpScrEnd, emitMosaicNode, hpPreScr]; rw [hns]
    · dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]; rfl
    · dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]; rfl
    · dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]; rfl
    · dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r]; rfl
    · dsimp only [hpScrEnd, compScrEnd, sr5, sr4, sr3, sr2, sr1, hpPreScr, c7, c6, c5r, gAppEnd, gScrEnd]
      simp [hsid]; rfl
  obtain ⟨endSt, gApp, gScr, hrunFast, hjh', hclos, hns', hroot, htr, hgs, hcells, hnext,
    hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc⟩ := hFast
  refine ⟨endSt, gApp, gScr, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrunFast, hjh',
    hclos, hns', hroot, htr, hgs, hcells, hnext, hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc⟩

/-- Shared `CalculatorApp(ch = 1, defF = 3)` recomposition driver parameterized by the `CalculatorScreen` outcome. -/
private theorem CalculatorApp_recompose_core (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 150 ≤ subFuel) (hf : 200 ≤ fuel)
    (initArg cSt : CalculatorState) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (hgs : hp.composer.groupStack = [])
    (hcells : hp.composer.stateCells = [(0, .ext (.calcState cSt))])
    (hnext : hp.composer.nextStateId = 1)
    (gApp gScr : Compose.GroupEntry JvmVal)
    (hgroups : hp.composer.groups = [gApp, gScr])
    (hgAppKey : gApp.key = (54337357 : Int32))
    (hgAppSlots : gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)])
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hw : HasCalcWhenMappings jh)
    (scrClosures : Array (String × List JvmVal))
    (cidScrRestart : Nat)
    (hscr :
      let gAppRead : Compose.GroupEntry JvmVal :=
        if 0 ∈ gApp.reads then gApp else { gApp with reads := 0 :: gApp.reads }
      let comp5 : Compose.ComposerModel JvmVal := {
        inserting := false
        groups := [gAppRead, gScr]
        groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
        stateCells := [(0, .ext (.calcState cSt))]
        nextStateId := 1
        traceEnabled := false
      }
      let gScrNew : Compose.GroupEntry JvmVal := {
        gScr with
        slots := [.ext (.calcState cSt), .ext (.closureRef cidKey)]
        dirty := false
        restartClosure? := some (.ext (.closureRef cidScrRestart))
      }
      let compScrEnd : Compose.ComposerModel JvmVal := {
        inserting := false
        groups := [gAppRead, gScrNew]
        groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
        stateCells := [(0, .ext (.calcState cSt))]
        nextStateId := 1
        traceEnabled := false
      }
      ∃ stScr,
        Jvm.runJvmRes (mkCalcHooks calcProgLookup (d - 1) subFuel) subFuel CalculatorScreen_prog
            (initCalcJvmState
              [(0, .ext (.calcState cSt)), (1, .ext (.closureRef cidOnKey)),
               (2, .ext (.modifier none)), (3, .ext .composer), (4, .i32 432), (5, .i32 0)]
              { hp with composer := comp5 } jh) =
          some (.unit, stScr) ∧
        stScr.jvmHeap = jh ∧
        stScr.heap = {
          composer := compScrEnd
          closures := scrClosures
          nodeStack := []
          emittedRoot? := some (calculatorScreenMosaicNode cSt cidKey)
        }) :
    let cidAppRestart := scrClosures.size
    let closuresEnd :=
      scrClosures.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
        [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .ext .composer),
             (3, .i32 1), (4, .i32 3)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hcompStatic : jh.getStatic? "androidx/compose/runtime/Composer" "Companion" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  have hstableStatic :
      jh.getStatic? "com/alexvanyo/composelife/mosaiccalculator/CalculatorState" "$stable" = none :=
    hw.staticsClean _ _ (by decide) (by decide)
  have hneKeys : (gApp.key == (2094116101 : Int32)) = false := by rw [hgAppKey]; decide
  have heqApp : (gApp.key == (54337357 : Int32)) = true := by rw [hgAppKey]; decide
  have heqScr : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
  let c0 := Compose.startRestartGroup hp.composer 54337357
  let c1 := Compose.startDefaults c0
  let c2 := Compose.endDefaults (Compose.skipToGroupEnd c1)
  have hc0Groups : c0.groups = [gApp, gScr] := by
    dsimp only [c0, Compose.startRestartGroup]
    rw [hgroups]
    unfold_ui_priv
    simp [heqApp]
  have hc2Trace : c2.traceEnabled = false := by
    dsimp only [c2, c1]; rw [traceEnabled_endDefaults, traceEnabled_skipToGroupEnd, traceEnabled_startDefaults]
    exact htrace
  have hc2Eq : c2 = {
      inserting := false
      groups := [gApp, gScr]
      groupStack := [{ key := 54337357, cursor := 0, lastReadIdx? := none, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [c2, c1, c0, Compose.endDefaults, Compose.skipToGroupEnd, Compose.startDefaults,
      Compose.startRestartGroup]
    rw [hins, htrace, hgs, hcells, hnext, hgroups]
    unfold_ui_priv
    simp [heqApp]
  let r3 := Compose.readRememberSlot c2
  have hr3Val : r3.1 = some (.ext (.stateRef 0)) := by
    dsimp only [r3]
    rw [hc2Eq]
    dsimp only [Compose.readRememberSlot]
    unfold_ui_priv
    simp [heqApp, hgAppSlots]
  let c3 := r3.2
  have hc3Eq : c3 = {
      inserting := false
      groups := [gApp, gScr]
      groupStack := [{ key := 54337357, cursor := 1, lastReadIdx? := some 0, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [c3, r3]
    rw [hc2Eq]
    dsimp only [Compose.readRememberSlot]
    unfold_ui_priv
    simp [heqApp, hgAppSlots]
  let gAppRead : Compose.GroupEntry JvmVal :=
    if 0 ∈ gApp.reads then gApp else { gApp with reads := 0 :: gApp.reads }
  let c4 : Compose.ComposerModel JvmVal := {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack := [{ key := 54337357, cursor := 1, lastReadIdx? := some 0, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    }
  have hc3Read : Compose.readMutableState c3 0 = some (.ext (.calcState cSt), c4) := by
    rw [hc3Eq]
    dsimp only [Compose.readMutableState]
    unfold_ui_priv
    dsimp only [c4, gAppRead]
    try rw [heqApp]
    rfl
  have hlam1 := CalculatorApp_lambda_1_equiv_fuel (d' + 3) subFuel subFuel (by omega)
    (by omega) 0 { hp with composer := c3 } jh cSt c4 hc3Read
  have hgAppReadKey : gAppRead.key = (54337357 : Int32) := by
    dsimp only [gAppRead]; split <;> exact hgAppKey
  have heqAppRead : (gAppRead.key == (54337357 : Int32)) = true := by rw [hgAppReadKey]; decide
  have hgAppReadSlots : gAppRead.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] := by
    dsimp only [gAppRead]; split <;> exact hgAppSlots
  let r5 := Compose.readRememberSlot c4
  have hr5Val : r5.1 = some (.ext (.closureRef cidOnKey)) := by
    dsimp only [r5, Compose.readRememberSlot, c4]
    unfold_ui_priv
    simp [heqAppRead, hgAppReadSlots]
  let c5 := r5.2
  have hc5Eq : c5 = {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [c5, r5, Compose.readRememberSlot, c4]
    unfold_ui_priv
    simp [heqAppRead, hgAppReadSlots]
  let comp5 : Compose.ComposerModel JvmVal := {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    }
  have hc5Eq' : c5 = comp5 := by
    dsimp only [c5, r5, Compose.readRememberSlot, c4, comp5]
    unfold_ui_priv
    simp [heqAppRead, hgAppReadSlots]
  let cidAppRestart := scrClosures.size
  let gScrNew : Compose.GroupEntry JvmVal := {
    gScr with
    slots := [.ext (.calcState cSt), .ext (.closureRef cidKey)]
    dirty := false
    restartClosure? := some (.ext (.closureRef cidScrRestart))
  }
  let compScrEnd : Compose.ComposerModel JvmVal := {
      inserting := false
      groups := [gAppRead, gScrNew]
      groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    }
  let hpScrEnd : CalcHeap := {
    composer := compScrEnd
    closures := scrClosures
    nodeStack := []
    emittedRoot? := some (calculatorScreenMosaicNode cSt cidKey)
  }
  have htrScrEnd : hpScrEnd.composer.traceEnabled = false := rfl
  have hEndKey : (Compose.endRestartGroup hpScrEnd.composer).1 = some 54337357 := rfl
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState initArg)))
            1 (.ext (.modifier none)))
          2 (.ext .composer))
        3 (.i32 1))
      4 (.i32 3)
  have hl0 : locs0 0 = .ext (.calcState initArg) := rfl
  have hl1 : locs0 1 = .ext (.modifier none) := rfl
  have hl2 : locs0 2 = .ext .composer := rfl
  have hl3 : locs0 3 = .i32 1 := rfl
  have hl4 : locs0 4 = .i32 3 := rfl
  have hFast :
      ∃ (endSt : JvmState) (gApp' gScr' : Compose.GroupEntry JvmVal),
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 4) subFuel) (kF + 200)
            CalculatorApp_prog 0 CalculatorApp_prog ⟨0, [], locs0, jh, hp⟩ =
          some (.unit, endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.closures =
          scrClosures.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
            [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3]) ∧
        endSt.heap.nodeStack = [] ∧
        endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
        endSt.heap.composer.traceEnabled = false ∧
        endSt.heap.composer.groupStack = [] ∧
        endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
        endSt.heap.composer.nextStateId = 1 ∧
        endSt.heap.composer.groups = [gApp', gScr'] ∧
        gApp'.key = (54337357 : Int32) ∧
        gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
        gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
        gScr'.key = (2094116101 : Int32) ∧
        gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
        gScr'.dirty = false ∧
        gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
    dsimp only [CalculatorApp_prog]
    rw [runFast_aload, hl2, runFast_iconst, runFast_startRestartGroup, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_ldcStr, runFast_sourceInfo]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_iconst, runFast_iand, runFast_ifne_zero']
    rw [runFast_iload]; peel_loc; rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand]
    rw [runFast_ifne_nonzero' (by decide)]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_iconst, runFast_ior, runFast_istore]
    rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_ior, runFast_istore, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_iconst]
    rw [runFast_if_icmpeq_ne (by decide), runFast_iconst, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_shouldExecute']
    dsimp only
    rw [show Compose.startRestartGroup hp.composer (UInt32.toInt32 54337357) = c0 from rfl]
    simp only [Compose.shouldExecute, show ((1 : UInt32) != 0) = true from rfl, Bool.or_true, ↓reduceIte]
    rw [runFast_ifeq_nonzero (by decide)]
    rw [runFast_aload]; peel_loc; rw [runFast_startDefaults]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_aload]; peel_loc; rw [runFast_getDefaultsInvalid]
    rw [show Compose.getDefaultsInvalid (Compose.startDefaults c0) = false from by
      dsimp only [Compose.getDefaultsInvalid, Compose.startDefaults]
      cases c0.groupStack <;> exact hins]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_skipToGroupEnd]
    rw [runFast_iload]; peel_loc; rw [hl4, runFast_iconst, runFast_iand, runFast_ifeq_nonzero (by decide)]
    rw [runFast_iload]; peel_loc; rw [runFast_iconst, runFast_iand, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_endDefaults]
    rw [show Compose.endDefaults (Compose.skipToGroupEnd (Compose.startDefaults c0)) = c2 from rfl]
    rw [runFast_isTraceInProgress' (d' + 3) subFuel _ _ _ (hp := { hp with composer := c2 }) hc2Trace,
      runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_iconst, runFast_istore, runFast_iconst, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
    dsimp only
    rw [hr3Val]
    dsimp only [Option.getD]
    rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hcompStatic]; rfl),
      runFast_composerEmpty']
    rw [runFast_if_acmpne_ext_branch rfl]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_nop, runFast_nop, checkCast_mutableState, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_sourceInfoMarkerEnd]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_aload]; peel_loc
    rw [show (Compose.readRememberSlot c2).2 = c3 from rfl]
    rw [invoke_CalculatorApp_lambda_1_step hlam1]
    rw [runFast_aload]; peel_loc; rw [runFast_iconst, runFast_ldcStr, runFast_sourceInfoMarkerStart]
    rw [runFast_aload]; peel_loc; rw [runFast_astore, runFast_iconst, runFast_istore, runFast_iconst, runFast_istore]
    rw [runFast_aload]; peel_loc; rw [runFast_rememberedValue]
    dsimp only
    rw [hr5Val]
    dsimp only [Option.getD]
    rw [runFast_astore, runFast_iconst, runFast_istore, runFast_aload]; peel_loc
    rw [runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hcompStatic]; rfl),
      runFast_composerEmpty']
    rw [runFast_if_acmpne_ext_branch rfl]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_nop, runFast_nop, checkCast_function1, runFast_astore]
    rw [runFast_aload]; peel_loc; rw [runFast_sourceInfoMarkerEnd]
    rw [runFast_aload]; peel_loc
    rw [runFast_aload]; peel_loc; rw [hl1]
    rw [runFast_aload]; peel_loc
    rw [runFast_iconst,
      runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hstableStatic]; rfl),
      runFast_ior]
    rw [runFast_iconst, runFast_iload]; peel_loc; rw [runFast_iconst, runFast_ishl, runFast_iand, runFast_ior]
    rw [runFast_iconst]
    rw [show (48 : UInt32) ||| (0 : UInt32) ||| (896 : UInt32) &&&
        (((1 : UInt32) ||| (2 : UInt32) ||| (48 : UInt32)) &&& (4294967281 : UInt32)) <<<
          ((3 : UInt32) &&& (31 : UInt32)) = (432 : UInt32) from by decide]
    rw [show (Compose.readRememberSlot c4).2 = comp5 from hc5Eq']
    have hscr' : ∃ stScr,
        Jvm.runJvmRes (mkCalcHooks calcProgLookup (d' + 3) subFuel) subFuel CalculatorScreen_prog
            (initCalcJvmState
              [(0, .ext (.calcState cSt)), (1, .ext (.closureRef cidOnKey)),
               (2, .ext (.modifier none)), (3, .ext .composer), (4, .i32 432), (5, .i32 0)]
              { hp with composer := comp5 } jh) =
          some (.unit, stScr) ∧
        stScr.jvmHeap = jh ∧
        stScr.heap = hpScrEnd := hscr
    rw [invoke_CalculatorScreen_step hscr']
    rw [runFast_isTraceInProgress' (d' + 3) subFuel _ _ _ (hp := hpScrEnd) htrScrEnd, runFast_ifeq_zero]
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_aload]; peel_loc; rw [runFast_endRestartGroup]
    dsimp only
    rw [hEndKey]
    dsimp only
    rw [runFast_dup, runFast_ifnull_fallthrough' rfl]
    rw [runFast_aload]; peel_loc; rw [hl0, runFast_aload]; peel_loc; rw [hl1]
    rw [runFast_iload]; peel_loc; rw [hl3, runFast_iload]; peel_loc; rw [hl4]
    rw [runFast_invokedynamic_bsm4 parseTags_app_bsm4 bsm_CalculatorApp_lambda_4]
    dsimp only [allocClosure]
    rw [runFast_updateScope, runFast_goto']
    dsimp only [CalculatorApp_prog, List.drop]
    rw [runFast_vreturn']
    let gAppEnd : Compose.GroupEntry JvmVal := {
      gAppRead with
      dirty := false
      restartClosure? := some (.ext (.closureRef cidAppRestart))
    }
    refine ⟨_, gAppEnd, gScrNew, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl,
      hgScrKey, rfl, rfl, rfl⟩
    · dsimp only [Compose.setGroupRestartClosure, Compose.endRestartGroup, hpScrEnd, compScrEnd]
      unfold_ui_priv
      simp only [heqAppRead, ↓reduceIte]
      unfold_ui_priv
      simp [heqAppRead, gAppEnd, cidAppRestart]
    · exact hgAppReadKey
    · exact hgAppReadSlots
  obtain ⟨endSt, gApp', gScr', hrunFast, hjh', hclos, hns', hroot, htr, hgs', hcells', hnext',
    hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc⟩ := hFast
  refine ⟨endSt, gApp', gScr', Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrunFast, hjh',
    hclos, hns', hroot, htr, hgs', hcells', hnext', hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc⟩

/-- Core recomposition equivalence for `CalculatorApp(ch = 1, defF = 3)` when `oldSt ≠ cSt`. -/
theorem CalculatorApp_recompose_equiv (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 150 ≤ subFuel) (hf : 200 ≤ fuel)
    (initArg cSt oldSt : CalculatorState) (hne : oldSt ≠ cSt) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (hns : hp.nodeStack = [])
    (hgs : hp.composer.groupStack = [])
    (hcells : hp.composer.stateCells = [(0, .ext (.calcState cSt))])
    (hnext : hp.composer.nextStateId = 1)
    (gApp gScr : Compose.GroupEntry JvmVal)
    (hgroups : hp.composer.groups = [gApp, gScr])
    (hgAppKey : gApp.key = (54337357 : Int32))
    (hgAppSlots : gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)])
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState oldSt), .ext (.closureRef cidKey)])
    (hw : HasCalcWhenMappings jh)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    let cidCol := hp.closures.size
    let cidScrRestart := cidCol + 1
    let cidAppRestart := cidScrRestart + 1
    let closuresEnd :=
      ((hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]))
        |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
        |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .ext .composer),
             (3, .i32 1), (4, .i32 3)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  let gAppRead : Compose.GroupEntry JvmVal :=
    if 0 ∈ gApp.reads then gApp else { gApp with reads := 0 :: gApp.reads }
  let comp5 : Compose.ComposerModel JvmVal := {
    inserting := false
    groups := [gAppRead, gScr]
    groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
    stateCells := [(0, .ext (.calcState cSt))]
    nextStateId := 1
    traceEnabled := false
  }
  let hpPreScr : CalcHeap := { hp with composer := comp5 }
  have hgAppReadKey : gAppRead.key = (54337357 : Int32) := by
    dsimp only [gAppRead]; split <;> exact hgAppKey
  have hneAppRead209 : (gAppRead.key == (2094116101 : Int32)) = false := by
    rw [hgAppReadKey]; decide
  have heqScr : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
  have hscrRaw := CalculatorScreen_recompose_equiv (d - 1) subFuel subFuel (by omega) (by omega)
    (by omega) oldSt cSt hne (.ext (.closureRef cidOnKey)) rfl cidKey hpPreScr jh
    rfl rfl gScr hgScrKey hgScrSlots (.inr ⟨gAppRead, rfl, hgAppReadKey⟩)
    hw.errSwitch hw.staticsClean hsing
  obtain ⟨stScr, hrunScr, hjhScr, hhpScr⟩ := hscrRaw
  let gScr1 : Compose.GroupEntry JvmVal := {
    gScr with
    slots := [.ext (.calcState cSt), .ext (.closureRef cidKey)]
  }
  let gScrNew : Compose.GroupEntry JvmVal := {
    gScr with
    slots := [.ext (.calcState cSt), .ext (.closureRef cidKey)]
    dirty := false
    restartClosure? := some (.ext (.closureRef (hp.closures.size + 1)))
  }
  let compScrEnd : Compose.ComposerModel JvmVal := {
    inserting := false
    groups := [gAppRead, gScrNew]
    groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
    stateCells := [(0, .ext (.calcState cSt))]
    nextStateId := 1
    traceEnabled := false
  }
  let sr1 := Compose.startRestartGroup comp5 2094116101
  let sr2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) sr1 (.ext (.calcState cSt))).2
  let sr3 := (Compose.readRememberSlot sr2).2
  let sr4 := (Compose.endRestartGroup sr3).2
  have hsr1Eq : sr1 = {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack :=
        [{ key := 2094116101, cursor := 0, lastReadIdx? := none, inDefaults := false, skipped := false },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr1, Compose.startRestartGroup, comp5]
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte]
  have hsr2Eq : sr2 = {
      inserting := false
      groups := [gAppRead, gScr1]
      groupStack :=
        [{ key := 2094116101, cursor := 1, lastReadIdx? := none, inDefaults := false, skipped := false },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr2, Compose.checkChangedSlot]
    rw [hsr1Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
    unfold_ui_priv
    dsimp only [gScr1]
  have hgScr1Key : (gScr1.key == (2094116101 : Int32)) = true := heqScr
  have hsr3Eq : sr3 = {
      inserting := false
      groups := [gAppRead, gScr1]
      groupStack :=
        [{ key := 2094116101, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr3, Compose.readRememberSlot]
    rw [hsr2Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, hgScr1Key, Bool.false_eq_true, ↓reduceIte]
  have hsr4Eq : sr4 = {
      inserting := false
      groups := [gAppRead, { gScr1 with dirty := false }]
      groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr4, Compose.endRestartGroup]
    rw [hsr3Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, hgScr1Key, Bool.false_eq_true, ↓reduceIte]
  have hcompScrEndEq :
      Compose.setGroupRestartClosure sr4 2094116101 (.ext (.closureRef (hp.closures.size + 1))) = compScrEnd := by
    dsimp only [Compose.setGroupRestartClosure, compScrEnd]
    rw [hsr4Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, hgScr1Key, Bool.false_eq_true, ↓reduceIte]
    dsimp only [gScrNew, gScr1]
  have hhpScrEq : stScr.heap = {
      composer := compScrEnd
      closures := (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0])
      nodeStack := []
      emittedRoot? := some (calculatorScreenMosaicNode cSt cidKey)
    } := by
    rw [hhpScr]
    dsimp only [emitMosaicNode, hpPreScr]
    rw [hns]
    dsimp only [sr4, sr3, sr2, sr1] at hcompScrEndEq ⊢
    rw [hcompScrEndEq]
  dsimp only
  simpa [Array.size_push] using
    CalculatorApp_recompose_core d subFuel fuel hd hsub hf initArg cSt cidOnKey cidKey hp jh
      hins htrace hgs hcells hnext gApp gScr hgroups hgAppKey hgAppSlots hgScrKey hw
      ((hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
      (hp.closures.size + 1)
      ⟨stScr, hrunScr, hjhScr, hhpScrEq⟩

/-- Core recomposition equivalence for `CalculatorApp(ch = 1, defF = 3)` when `oldSt = cSt` and `gScr` is clean
(`CalculatorScreen` takes the `skipToGroupEnd` fast path). -/
theorem CalculatorApp_recompose_skip_equiv (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 150 ≤ subFuel) (hf : 200 ≤ fuel)
    (initArg cSt : CalculatorState) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (hns : hp.nodeStack = [])
    (hgs : hp.composer.groupStack = [])
    (hcells : hp.composer.stateCells = [(0, .ext (.calcState cSt))])
    (hnext : hp.composer.nextStateId = 1)
    (hroot : hp.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey))
    (gApp gScr : Compose.GroupEntry JvmVal)
    (hgroups : hp.composer.groups = [gApp, gScr])
    (hgAppKey : gApp.key = (54337357 : Int32))
    (hgAppSlots : gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)])
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)])
    (hgScrClean : gScr.dirty = false)
    (hw : HasCalcWhenMappings jh) :
    let cidScrRestart := hp.closures.size
    let cidAppRestart := cidScrRestart + 1
    let closuresEnd :=
      (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
        [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
        |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .ext .composer),
             (3, .i32 1), (4, .i32 3)]
            hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  let gAppRead : Compose.GroupEntry JvmVal :=
    if 0 ∈ gApp.reads then gApp else { gApp with reads := 0 :: gApp.reads }
  let comp5 : Compose.ComposerModel JvmVal := {
    inserting := false
    groups := [gAppRead, gScr]
    groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
    stateCells := [(0, .ext (.calcState cSt))]
    nextStateId := 1
    traceEnabled := false
  }
  let hpPreScr : CalcHeap := { hp with composer := comp5 }
  have hgAppReadKey : gAppRead.key = (54337357 : Int32) := by
    dsimp only [gAppRead]; split <;> exact hgAppKey
  have hneAppRead209 : (gAppRead.key == (2094116101 : Int32)) = false := by
    rw [hgAppReadKey]; decide
  have heqScr : (gScr.key == (2094116101 : Int32)) = true := by rw [hgScrKey]; decide
  have hscrRaw := CalculatorScreen_skip_equiv_ch (d - 1) subFuel subFuel (by omega) (by omega)
    432 (Or.inr rfl) cSt (.ext (.closureRef cidOnKey)) rfl cidKey hpPreScr jh rfl gScr hgScrKey hgScrSlots
    hgScrClean (.inr ⟨gAppRead, rfl, hgAppReadKey⟩)
  obtain ⟨stScr, hrunScr, hjhScr, hhpScr⟩ := hscrRaw
  let gScrNew : Compose.GroupEntry JvmVal := {
    gScr with
    slots := [.ext (.calcState cSt), .ext (.closureRef cidKey)]
    dirty := false
    restartClosure? := some (.ext (.closureRef hp.closures.size))
  }
  let compScrEnd : Compose.ComposerModel JvmVal := {
    inserting := false
    groups := [gAppRead, gScrNew]
    groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
    stateCells := [(0, .ext (.calcState cSt))]
    nextStateId := 1
    traceEnabled := false
  }
  let sr1 := Compose.startRestartGroup comp5 2094116101
  let sr2 := (Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) sr1 (.ext (.calcState cSt))).2
  let sr3 := Compose.skipToGroupEnd sr2
  let sr4 := (Compose.endRestartGroup sr3).2
  have hsr1Eq : sr1 = {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack :=
        [{ key := 2094116101, cursor := 0, lastReadIdx? := none, inDefaults := false, skipped := false },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr1, Compose.startRestartGroup, comp5]
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte]
  have hsr2Eq : sr2 = {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack :=
        [{ key := 2094116101, cursor := 1, lastReadIdx? := none, inDefaults := false, skipped := false },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr2, Compose.checkChangedSlot]
    rw [hsr1Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte, hgScrSlots, List.getElem?_cons_zero]
    unfold_ui_priv
    rw [← hgScrSlots]
  have hsr3Eq : sr3 = {
      inserting := false
      groups := [gAppRead, gScr]
      groupStack :=
        [{ key := 2094116101, cursor := 1, lastReadIdx? := none, inDefaults := false, skipped := true },
         { key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr3, Compose.skipToGroupEnd]
    rw [hsr2Eq]
    dsimp only
    rfl
  have hsr4Eq : sr4 = {
      inserting := false
      groups := [gAppRead, { gScr with dirty := false }]
      groupStack := [{ key := 54337357, cursor := 2, lastReadIdx? := some 1, inDefaults := false, skipped := false }]
      stateCells := [(0, .ext (.calcState cSt))]
      nextStateId := 1
      traceEnabled := false
    } := by
    dsimp only [sr4, Compose.endRestartGroup]
    rw [hsr3Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte]
  have hcompScrEndEq :
      Compose.setGroupRestartClosure sr4 2094116101 (.ext (.closureRef hp.closures.size)) = compScrEnd := by
    dsimp only [Compose.setGroupRestartClosure, compScrEnd]
    rw [hsr4Eq]; dsimp only
    unfold_ui_priv
    simp only [hneAppRead209, heqScr, Bool.false_eq_true, ↓reduceIte]
    dsimp only [gScrNew]
    rw [← hgScrSlots]
  have hhpScrEq : stScr.heap = {
      composer := compScrEnd
      closures := hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
        [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0])
      nodeStack := []
      emittedRoot? := some (calculatorScreenMosaicNode cSt cidKey)
    } := by
    rw [hhpScr]
    dsimp only [hpPreScr]
    rw [hns, hroot]
    dsimp only [sr4, sr3, sr2, sr1] at hcompScrEndEq ⊢
    rw [hcompScrEndEq]
  dsimp only
  simpa [Array.size_push] using
    CalculatorApp_recompose_core d subFuel fuel hd hsub hf initArg cSt cidOnKey cidKey hp jh
      hins htrace hgs hcells hnext gApp gScr hgroups hgAppKey hgAppSlots hgScrKey hw
      (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
        [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
      hp.closures.size
      ⟨stScr, hrunScr, hjhScr, hhpScrEq⟩

set_option maxRecDepth 4096 in
/-- Shared bytecode equivalence driver for `CalculatorScreenKt.CalculatorApp$lambda$4` (recompose wrapper). -/
private theorem CalculatorApp_lambda_4_core (d subFuel fuel : Nat)
    (hd : 5 ≤ d) (hf : 20 ≤ fuel)
    (initArg cSt : CalculatorState) (chArg unusedFlags : UInt32)
    (hch : chArg = 0 ∨ chArg = 1) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hw : HasCalcWhenMappings jh)
    (scrClosures : Array (String × List JvmVal)) (cidScrRestart : Nat)
    (hApp :
      let cidAppRestart := scrClosures.size
      let closuresEnd :=
        scrClosures.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
      ∃ endSt gApp' gScr',
        Jvm.runJvmRes (mkCalcHooks calcProgLookup (d - 1) subFuel) subFuel CalculatorApp_prog
            (initCalcJvmState
              [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .ext .composer),
               (3, .i32 1), (4, .i32 3)]
              hp jh) =
          some (.unit, endSt) ∧
        endSt.jvmHeap = jh ∧
        endSt.heap.closures = closuresEnd ∧
        endSt.heap.nodeStack = [] ∧
        endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
        endSt.heap.composer.traceEnabled = false ∧
        endSt.heap.composer.groupStack = [] ∧
        endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
        endSt.heap.composer.nextStateId = 1 ∧
        endSt.heap.composer.groups = [gApp', gScr'] ∧
        gApp'.key = (54337357 : Int32) ∧
        gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
        gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
        gScr'.key = (2094116101 : Int32) ∧
        gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
        gScr'.dirty = false ∧
        gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart))) :
    let cidAppRestart := scrClosures.size
    let closuresEnd :=
      scrClosures.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
        [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_4_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .i32 chArg), (3, .i32 3),
             (4, .ext .composer), (5, .i32 unusedFlags)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  obtain ⟨stApp, gApp', gScr', hrunApp, hjhApp, hclos, hns', hroot, htr', hgs', hcells', hnext',
    hgr', hgk', hgsl', hgrc', hsk', hssl', hsd', hsrc'⟩ := hApp
  have hupd : Compose.updateChangedFlags (chArg ||| 1) = 1 := by
    rcases hch with rfl | rfl <;> decide
  let locs0 : Nat → JvmVal :=
    @setLocal CalcExt
      (@setLocal CalcExt
        (@setLocal CalcExt
          (@setLocal CalcExt
            (@setLocal CalcExt
              (@setLocal CalcExt (fun _ => .i32 0) 0 (.ext (.calcState initArg)))
              1 (.ext (.modifier none)))
            2 (.i32 chArg))
          3 (.i32 3))
        4 (.ext .composer))
      5 (.i32 unusedFlags)
  have hl0 : locs0 0 = .ext (.calcState initArg) := rfl
  have hl1 : locs0 1 = .ext (.modifier none) := rfl
  have hl2 : locs0 2 = .i32 chArg := rfl
  have hl3 : locs0 3 = .i32 3 := rfl
  have hl4 : locs0 4 = .ext .composer := rfl
  have hAppStep : ∀ {f0 pc0 : Nat} {prog0 rest0 : List JvmInstr} {stk0 : List JvmVal}
      {locs : Nat → JvmVal},
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 5) subFuel) (f0 + 1) prog0 pc0
          (.invokestatic "CalculatorScreenKt" "CalculatorApp"
            "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" ::
            rest0)
          ⟨pc0, .i32 3 :: .i32 1 :: .ext .composer :: .ext (.modifier none) :: .ext (.calcState initArg) :: stk0,
            locs, jh, hp⟩ =
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 5) subFuel) f0 prog0 (pc0 + 1) rest0
          ⟨pc0 + 1, stk0, locs, stApp.jvmHeap, stApp.heap⟩ := by
    intro f0 pc0 prog0 rest0 stk0 locs
    refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
    change (mkCalcHooks calcProgLookup (d' + 5) subFuel).stepInvokeStatic _ _ _ _ = _
    conv => lhs; whnf
    unfold_ui_priv
    dsimp only
    rw [show "CalculatorScreenKt" ++ "." ++ "CalculatorApp" = "CalculatorScreenKt.CalculatorApp"
      from by apply String.ext; simp]
    rw [show Jvm.parseMethodParamTags
        "(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/modifier/Modifier;Landroidx/compose/runtime/Composer;II)V" =
        ['L', 'L', 'L', 'I', 'I'] from by decide]
    dsimp only [List.length]
    cases (stk0.length + 5).decLt 5 with
    | isTrue h => omega
    | isFalse _ =>
      dsimp only [List.take, List.drop, List.reverse, List.reverseAux]
      rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp" = some CalculatorApp_prog from rfl]
      unfold_ui_priv
      dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl] at hrunApp ⊢
      rw [show d' + 5 - 1 = d' + 4 from rfl] at hrunApp
      rw [hrunApp]
      simp only [↓reduceIte]
  have hunitClean : stApp.jvmHeap.getStatic? "kotlin/Unit" "INSTANCE" = none := by
    rw [hjhApp]; exact hw.staticsClean _ _ (by decide) (by decide)
  have hFast : ∃ endSt : JvmState,
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 5) subFuel) (kF + 20)
          CalculatorApp_lambda_4_prog 0 CalculatorApp_lambda_4_prog ⟨0, [], locs0, jh, hp⟩ =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = stApp.heap := by
    dsimp only [CalculatorApp_lambda_4_prog]
    rw [runFast_aload, hl0, runFast_aload, hl1, runFast_aload, hl4, runFast_iload, hl2,
      runFast_iconst, runFast_ior, runFast_updateChangedFlags, hupd, runFast_iload, hl3,
      hAppStep,
      runFast_getstatic_calcClean (by dsimp only [Jvm.stepInstr]; rw [hunitClean]; rfl),
      runFast_areturn']
    exact ⟨_, rfl, hjhApp, rfl⟩
  obtain ⟨endSt, hrunFast, hjhEnd, hhpEnd⟩ := hFast
  refine ⟨endSt, gApp', gScr', Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hrunFast, hjhEnd, ?_⟩
  rw [hhpEnd]
  exact ⟨hclos, hns', hroot, htr', hgs', hcells', hnext', hgr', hgk', hgsl', hgrc', hsk', hssl', hsd', hsrc'⟩

/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorApp$lambda$4` when `oldSt ≠ cSt`. -/
theorem CalculatorApp_lambda_4_equiv (d subFuel fuel : Nat)
    (hd : 5 ≤ d) (hsub : 200 ≤ subFuel) (hf : 20 ≤ fuel)
    (initArg cSt oldSt : CalculatorState) (hne : oldSt ≠ cSt) (chArg unusedFlags : UInt32)
    (hch : chArg = 0 ∨ chArg = 1) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (hns : hp.nodeStack = [])
    (hgs : hp.composer.groupStack = [])
    (hcells : hp.composer.stateCells = [(0, .ext (.calcState cSt))])
    (hnext : hp.composer.nextStateId = 1)
    (gApp gScr : Compose.GroupEntry JvmVal)
    (hgroups : hp.composer.groups = [gApp, gScr])
    (hgAppKey : gApp.key = (54337357 : Int32))
    (hgAppSlots : gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)])
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState oldSt), .ext (.closureRef cidKey)])
    (hw : HasCalcWhenMappings jh)
    (hsing : HasSingletonRowLambdas jh hp.closures) :
    let cidCol := hp.closures.size
    let cidScrRestart := cidCol + 1
    let cidAppRestart := cidScrRestart + 1
    let closuresEnd :=
      ((hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)]))
        |>.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
        |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_4_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .i32 chArg), (3, .i32 3),
             (4, .ext .composer), (5, .i32 unusedFlags)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  dsimp only
  simpa [Array.size_push] using
    CalculatorApp_lambda_4_core d subFuel fuel hd hf initArg cSt chArg unusedFlags hch cidOnKey cidKey hp jh hw
      ((hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1", [.ext (.calcState cSt)])).push
        ("CalculatorScreenKt.CalculatorScreen$lambda$2",
          [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
      (hp.closures.size + 1)
      (by
        have hApp := CalculatorApp_recompose_equiv (d - 1) subFuel subFuel (by omega) (by omega) (by omega)
          initArg cSt oldSt hne cidOnKey cidKey hp jh hins htrace hns hgs hcells hnext gApp gScr hgroups
          hgAppKey hgAppSlots hgScrKey hgScrSlots hw hsing
        simpa [Array.size_push] using hApp)

/-- Bytecode equivalence theorem for `CalculatorScreenKt.CalculatorApp$lambda$4` when `oldSt = cSt` and `gScr` is clean. -/
theorem CalculatorApp_lambda_4_skip_equiv (d subFuel fuel : Nat)
    (hd : 5 ≤ d) (hsub : 200 ≤ subFuel) (hf : 20 ≤ fuel)
    (initArg cSt : CalculatorState) (chArg unusedFlags : UInt32)
    (hch : chArg = 0 ∨ chArg = 1) (cidOnKey cidKey : Nat)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (hins : hp.composer.inserting = false)
    (htrace : hp.composer.traceEnabled = false)
    (hns : hp.nodeStack = [])
    (hgs : hp.composer.groupStack = [])
    (hcells : hp.composer.stateCells = [(0, .ext (.calcState cSt))])
    (hnext : hp.composer.nextStateId = 1)
    (hroot : hp.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey))
    (gApp gScr : Compose.GroupEntry JvmVal)
    (hgroups : hp.composer.groups = [gApp, gScr])
    (hgAppKey : gApp.key = (54337357 : Int32))
    (hgAppSlots : gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)])
    (hgScrKey : gScr.key = (2094116101 : Int32))
    (hgScrSlots : gScr.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)])
    (hgScrClean : gScr.dirty = false)
    (hw : HasCalcWhenMappings jh) :
    let cidScrRestart := hp.closures.size
    let cidAppRestart := cidScrRestart + 1
    let closuresEnd :=
      (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
        [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
        |>.push ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState initArg), .ext (.modifier none), .i32 1, .i32 3])
    ∃ endSt gApp' gScr',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_lambda_4_prog
          (initCalcJvmState
            [(0, .ext (.calcState initArg)), (1, .ext (.modifier none)), (2, .i32 chArg), (3, .i32 3),
             (4, .ext .composer), (5, .i32 unusedFlags)]
            hp jh) =
        some (.ext .unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap.closures = closuresEnd ∧
      endSt.heap.nodeStack = [] ∧
      endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey) ∧
      endSt.heap.composer.traceEnabled = false ∧
      endSt.heap.composer.groupStack = [] ∧
      endSt.heap.composer.stateCells = [(0, .ext (.calcState cSt))] ∧
      endSt.heap.composer.nextStateId = 1 ∧
      endSt.heap.composer.groups = [gApp', gScr'] ∧
      gApp'.key = (54337357 : Int32) ∧
      gApp'.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
      gApp'.restartClosure? = some (.ext (.closureRef cidAppRestart)) ∧
      gScr'.key = (2094116101 : Int32) ∧
      gScr'.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
      gScr'.dirty = false ∧
      gScr'.restartClosure? = some (.ext (.closureRef cidScrRestart)) := by
  dsimp only
  simpa [Array.size_push] using
    CalculatorApp_lambda_4_core d subFuel fuel hd hf initArg cSt chArg unusedFlags hch cidOnKey cidKey hp jh hw
      (hp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
        [.ext (.calcState cSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0]))
      hp.closures.size
      (by
        have hApp := CalculatorApp_recompose_skip_equiv (d - 1) subFuel subFuel (by omega) (by omega) (by omega)
          initArg cSt cidOnKey cidKey hp jh hins htrace hns hgs hcells hnext hroot gApp gScr hgroups
          hgAppKey hgAppSlots hgScrKey hgScrSlots hgScrClean hw
        simpa [Array.size_push] using hApp)

/-! ### End-to-End Composition + Key-Dispatch + Recomposition Invariant & Terminal Screen Theorems -/

/-- Valid post-composition heap invariant linking Compose runtime state, closure table, and Mosaic tree. -/
structure ValidCalculatorAppHeap (cSt : CalculatorState) (jh : Jvm.JvmHeap CalcExt) (hp : CalcHeap) : Prop where
  whenMappings : HasCalcWhenMappings jh
  singletonLambdas : HasSingletonRowLambdas jh hp.closures
  traceDisabled : hp.composer.traceEnabled = false
  emptyNodeStack : hp.nodeStack = []
  emptyGroupStack : hp.composer.groupStack = []
  stateCellsEq : hp.composer.stateCells = [(0, .ext (.calcState cSt))]
  nextStateIdEq : hp.composer.nextStateId = 1
  groupsShape : ∃ gApp gScr cidOnKey cidKey appRestart scrRestart chFlag,
    hp.composer.groups = [gApp, gScr] ∧
    gApp.key = (54337357 : Int32) ∧
    gApp.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
    gApp.restartClosure? = some (.ext (.closureRef appRestart)) ∧
    gScr.key = (2094116101 : Int32) ∧
    gScr.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
    gScr.dirty = false ∧
    gScr.restartClosure? = some (.ext (.closureRef scrRestart)) ∧
    hp.closures[cidOnKey]? = some ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]) ∧
    hp.closures[cidKey]? = some ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [.ext (.closureRef cidOnKey)]) ∧
    (chFlag = 0 ∨ chFlag = 1) ∧
    hp.closures[appRestart]? = some ("CalculatorScreenKt.CalculatorApp$lambda$4",
      [.ext (.calcState .initial), .ext (.modifier none), .i32 chFlag, .i32 3]) ∧
    hp.emittedRoot? = some (calculatorScreenMosaicNode cSt cidKey)

private theorem calculatorScreenMosaicNode_keyHandler (cSt : CalculatorState) (cidKey : Nat) :
    Mosaic.findKeyHandler? (calculatorScreenMosaicNode cSt cidKey) = some cidKey :=
  rfl

private theorem ite_ne_newline (P : Prop) [Decidable P] (a b : Char)
    (ha : a ≠ '\n') (hb : b ≠ '\n') : (if P then a else b) ≠ '\n' := by
  split <;> assumption

private theorem digitChar_ne_newline (d : Nat) : Nat.digitChar d ≠ '\n' := by
  unfold Nat.digitChar
  repeat (first | apply ite_ne_newline; decide | decide)

private theorem toDigitsCore_no_newline (n fuel : Nat) (acc : List Char)
    (hacc : '\n' ∉ acc) : '\n' ∉ Nat.toDigitsCore 10 fuel n acc := by
  induction fuel generalizing n acc with
  | zero => exact hacc
  | succ f ih =>
    dsimp only [Nat.toDigitsCore]
    have hdig : '\n' ∉ Nat.digitChar (n % 10) :: acc := by
      intro hmem
      rcases List.mem_cons.mp hmem with h1 | h2
      · exact digitChar_ne_newline (n % 10) h1.symm
      · exact hacc h2
    split
    · exact hdig
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) hdig

private theorem natRepr_no_newline (n : Nat) : '\n' ∉ (Nat.repr n).toList := by
  dsimp only [Nat.repr, Nat.toDigits]
  rw [String.toList_ofList]
  exact toDigitsCore_no_newline n (n + 1) [] (by simp)

private theorem int64ToString_no_newline (v : Int64) : '\n' ∉ (int64ToString v).toList := by
  dsimp only [int64ToString, toString, instToStringInt, Int.repr]
  split
  · exact natRepr_no_newline _
  · rw [String.toList_append]
    intro hmem
    rcases List.mem_append.mp hmem with hm | hn
    · revert hm; decide
    · exact natRepr_no_newline _ hn

private theorem gt_formatDisplayLineModel_no_newline (state : CalculatorState) :
    '\n' ∉ (s!"> {formatDisplayLineModel state}").toList := by
  dsimp only [toString, instToStringString]
  rw [String.toList_append]
  intro hmem
  rcases List.mem_append.mp hmem with hgt | hfmt
  · revert hgt; decide
  · unfold formatDisplayLineModel at hfmt
    cases hErr : state.error with
    | some e =>
      rw [hErr] at hfmt
      cases e <;> (dsimp only at hfmt; exact (by revert hfmt; decide))
    | none =>
      rw [hErr] at hfmt
      cases hOpnd : state.pendingOperand with
      | none =>
        rw [hOpnd] at hfmt
        exact int64ToString_no_newline _ hfmt
      | some lhs =>
        rw [hOpnd] at hfmt
        cases hOp : state.pendingOp with
        | none =>
          rw [hOp] at hfmt
          exact int64ToString_no_newline _ hfmt
        | some op =>
          rw [hOp] at hfmt
          have hop : '\n' ∉ op.symbol.toList := by cases op <;> decide
          simp only [toString, String.toList_append, List.mem_append] at hfmt
          rcases hfmt with ((((hl | hs1) | hs2) | hs3) | hr)
          · exact int64ToString_no_newline _ hl
          · exact (by revert hs1; decide)
          · exact hop hs2
          · exact (by revert hs3; decide)
          · exact int64ToString_no_newline _ hr

private theorem array_push2_getElem?_lt {α : Type} (arr : Array α) (a b : α) {i : Nat}
    (hi : i < arr.size) :
    ((arr.push a).push b)[i]? = arr[i]? := by
  have hi1 : i < (arr.push a).size := by simp; omega
  rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hi1,
    Array.getElem_push_lt hi, ← Array.getElem?_eq_getElem hi]

private theorem array_push3_getElem?_lt {α : Type} (arr : Array α) (a b c : α) {i : Nat}
    (hi : i < arr.size) :
    (((arr.push a).push b).push c)[i]? = arr[i]? := by
  have hi1 : i < (arr.push a).size := by simp; omega
  have hi2 : i < ((arr.push a).push b).size := by simp; omega
  rw [Array.getElem?_eq_getElem (by simp; omega), Array.getElem_push_lt hi2,
    Array.getElem_push_lt hi1, Array.getElem_push_lt hi, ← Array.getElem?_eq_getElem hi]

private theorem calculatorScreenMosaicNode_render (cSt : CalculatorState) (cidKey : Nat) :
    Mosaic.renderMosaic (calculatorScreenMosaicNode cSt cidKey) = expectedCalculatorScreen cSt := by
  dsimp only [Mosaic.renderMosaic, calculatorScreenMosaicNode, Mosaic.renderMosaicLines,
    Mosaic.renderMosaicListLines]
  rw [Mosaic.splitLines_eq_singleton _ (gt_formatDisplayLineModel_no_newline cSt)]
  rfl

theorem ValidCalculatorAppHeap.renders_expected {cSt : CalculatorState} {jh : Jvm.JvmHeap CalcExt}
    {hp : CalcHeap} (hinv : ValidCalculatorAppHeap cSt jh hp) :
    ∃ tree,
      hp.emittedRoot? = some tree ∧
      Mosaic.renderMosaic tree = expectedCalculatorScreen cSt := by
  rcases hinv.groupsShape with ⟨_, _, _, cidKey, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hroot⟩
  exact ⟨calculatorScreenMosaicNode cSt cidKey, hroot, calculatorScreenMosaicNode_render cSt cidKey⟩

/-- Initial `CalculatorApp` bytecode composition establishes `ValidCalculatorAppHeap .initial` and renders
`expectedCalculatorScreen .initial`. -/
theorem CalculatorApp_initial_renders_expected (d subFuel fuel : Nat)
    (hd : 4 ≤ d) (hsub : 150 ≤ subFuel) (hf : 200 ≤ fuel) :
    ∃ endSt tree,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d subFuel) fuel CalculatorApp_prog
          (initCalcJvmState [(0, .null), (1, .null), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
            { closures := calcUiInitClosures } calcUiInitJvmHeap) =
        some (.unit, endSt) ∧
      ValidCalculatorAppHeap .initial endSt.jvmHeap endSt.heap ∧
      endSt.heap.emittedRoot? = some tree ∧
      Mosaic.renderMosaic tree = expectedCalculatorScreen .initial := by
  have hInit := CalculatorApp_initial_equiv d subFuel fuel hd hsub hf .null .null
    { closures := calcUiInitClosures } calcUiInitJvmHeap rfl rfl
    calcUiInitJvmHeap_hasWhenMappings calcUiInit_hasSingletonRowLambdas
  obtain ⟨endSt, gApp, gScr, hrun, hjh, hclos, hns, hroot, htr, hgs, hcells, hnext,
    hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc⟩ := hInit
  let hp0 : CalcHeap := { closures := calcUiInitClosures }
  let cidOnKey := hp0.closures.size
  let cidKey := cidOnKey + 1
  let cidCol := cidKey + 1
  let cidScrRestart := cidCol + 1
  let cidAppRestart := cidScrRestart + 1
  have hsingEnd : HasSingletonRowLambdas endSt.jvmHeap endSt.heap.closures := by
    rw [hjh, hclos]
    exact ⟨0, 1, 2, 3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hInv : ValidCalculatorAppHeap .initial endSt.jvmHeap endSt.heap := {
    whenMappings := by rw [hjh]; exact calcUiInitJvmHeap_hasWhenMappings
    singletonLambdas := hsingEnd
    traceDisabled := htr
    emptyNodeStack := hns
    emptyGroupStack := hgs
    stateCellsEq := hcells
    nextStateIdEq := hnext
    groupsShape := by
      refine ⟨gApp, gScr, cidOnKey, cidKey, cidAppRestart, cidScrRestart, 0,
        hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc, ?_, ?_, Or.inl rfl, ?_, hroot⟩
      · rw [hclos]; rfl
      · rw [hclos]; rfl
      · rw [hclos]; rfl
  }
  exact ⟨endSt, calculatorScreenMosaicNode .initial cidKey, hrun, hInv, hroot,
    calculatorScreenMosaicNode_render .initial cidKey⟩

/-- One key-dispatch + recomposition cycle on JVM preserves `ValidCalculatorAppHeap` and renders the
exact updated `expectedCalculatorScreen`. -/
theorem CalculatorApp_dispatchKeyEvent_and_recompose (depth fuel : Nat)
    (hd : 6 ≤ depth) (hf : 200 ≤ fuel)
    (cSt : CalculatorState) (keyStr : String) (st : JvmState)
    (hinv : ValidCalculatorAppHeap cSt st.jvmHeap st.heap) :
    let expectedSt := match mapTerminalKeyModel keyStr with
      | some k => reduceCalculatorStateModel cSt k
      | none => cSt
    ∃ handled endSt tree,
      dispatchKeyEventJvm calcProgLookup depth fuel keyStr st = some (handled, endSt) ∧
      handled = (mapTerminalKeyModel keyStr).isSome ∧
      (match mapTerminalKeyModel keyStr with
       | none =>
         ValidCalculatorAppHeap expectedSt endSt.jvmHeap endSt.heap ∧
         endSt.heap.emittedRoot? = some tree ∧
         Mosaic.renderMosaic tree = expectedCalculatorScreen expectedSt
       | some _ =>
         ∃ recompSt,
           recomposeAppJvm calcProgLookup depth fuel endSt = some recompSt ∧
           ValidCalculatorAppHeap expectedSt recompSt.jvmHeap recompSt.heap ∧
           recompSt.heap.emittedRoot? = some tree ∧
           Mosaic.renderMosaic tree = expectedCalculatorScreen expectedSt) := by
  intro expectedSt
  rcases hinv.groupsShape with ⟨gApp, gScr, cidOnKey, cidKey, appRestart, scrRestart, chFlag,
    hgr, hgk, hgsl, hgrc, hsk, hssl, hsd, hsrc, hClosOnKey, hClosKey, hch, hClosApp, hroot⟩
  have hdispHandler : st.heap.emittedRoot?.bind Mosaic.findKeyHandler? = some cidKey := by
    rw [hroot]; rfl
  have hInvoke : ∀ k : CalculatorKey,
      ∃ hp' jh' res subEnd,
        st.heap.closures[cidOnKey]? = some ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]) ∧
        calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$3$0" = some CalculatorApp_lambda_3_0_prog ∧
        Jvm.runJvmRes (mkCalcHooks calcProgLookup (depth - 1) fuel) fuel CalculatorApp_lambda_3_0_prog
            (initCalcJvmState [(0, .ext (.stateRef 0)), (1, .ext (.calcKey k))] st.heap st.jvmHeap) =
          some (res, subEnd) ∧
        subEnd.jvmHeap = jh' ∧ subEnd.heap = hp' := by
    intro k
    have hread : Compose.readMutableState st.heap.composer 0 =
        some (.ext (.calcState cSt), st.heap.composer) := by
      dsimp only [Compose.readMutableState]
      rw [hinv.stateCellsEq, hinv.emptyGroupStack]
      unfold_ui_priv
      dsimp only [List.find?]
      rw [show (0 == 0) = true from rfl, ← hinv.stateCellsEq]
      dsimp only
      rw [← hinv.emptyGroupStack]
    let newSt := reduceCalculatorStateModel cSt k
    let comp2 : Compose.ComposerModel JvmVal :=
      if (Jvm.JvmVal.beqVal beqCalcExt) (.ext (.calcState cSt)) (.ext (.calcState newSt)) then
        st.heap.composer
      else
        { st.heap.composer with
          stateCells := [(0, .ext (.calcState newSt))]
          groups := st.heap.composer.groups.map fun g =>
            if 0 ∈ g.reads then { g with dirty := true } else g }
    have hwrite : Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt) st.heap.composer 0
        (.ext (.calcState newSt)) = some comp2 := by
      dsimp only [Compose.writeMutableState]
      rw [hinv.stateCellsEq]
      dsimp only [List.find?]
      rw [show (0 == 0) = true from rfl]
      cases hbeq : (Jvm.JvmVal.beqVal beqCalcExt (.ext (.calcState cSt)) (.ext (.calcState newSt))) <;>
        dsimp only [comp2] <;> simp [hbeq]
    have h30 := CalculatorApp_lambda_3_0_equiv (depth - 1) fuel fuel (by omega) (by omega) (by omega)
      0 k cSt st.heap st.jvmHeap hinv.whenMappings st.heap.composer comp2 hread hwrite
    obtain ⟨subEnd, hrun30, hjh30, hhp30⟩ := h30
    exact ⟨{ st.heap with composer := comp2 }, st.jvmHeap, .ext .unit, subEnd, hClosOnKey, rfl,
      hrun30, hjh30, hhp30⟩
  have hScreenLam := CalculatorScreen_lambda_0_0_equiv depth fuel fuel (by omega) (by omega) (by omega)
    cidOnKey keyStr st.heap st.jvmHeap hinv.whenMappings.staticsClean
    "CalculatorScreenKt.CalculatorApp$lambda$3$0" (some (.ext (.stateRef 0)))
    CalculatorApp_lambda_3_0_prog hInvoke
  obtain ⟨dispEndSt, handled, hDispRun, hMatch⟩ := hScreenLam
  have hdispEq : dispatchKeyEventJvm calcProgLookup depth fuel keyStr st =
      some (handled, { st with jvmHeap := dispEndSt.jvmHeap, heap := dispEndSt.heap }) := by
    dsimp only [dispatchKeyEventJvm]
    rw [hdispHandler]
    dsimp only [Option.toList]
    rw [hClosKey]
    dsimp only
    rw [show calcProgLookup "CalculatorScreenKt.CalculatorScreen$lambda$0$0" =
      some CalculatorScreen_lambda_0_0_prog from rfl]
    dsimp only
    erw [hDispRun]
    cases handled <;> rfl
  cases hmap : mapTerminalKeyModel keyStr with
  | none =>
    rw [hmap] at hMatch
    rcases hMatch with ⟨rfl, hjh', hhp'⟩
    have hexp : expectedSt = cSt := by dsimp only [expectedSt]; rw [hmap]
    refine ⟨false, { st with jvmHeap := dispEndSt.jvmHeap, heap := dispEndSt.heap },
      calculatorScreenMosaicNode cSt cidKey, hdispEq, rfl, ?_⟩
    rw [hexp]
    refine ⟨?_, ?_, calculatorScreenMosaicNode_render cSt cidKey⟩
    · rw [hjh', hhp']; exact hinv
    · rw [hhp']; exact hroot
  | some k =>
    rw [hmap] at hMatch
    rcases hMatch with ⟨rfl, res0, subEnd, hClosOnKey', hTag', hRun30, hjhSub, hhpSub⟩
    have hread : Compose.readMutableState st.heap.composer 0 =
        some (.ext (.calcState cSt), st.heap.composer) := by
      dsimp only [Compose.readMutableState]
      rw [hinv.stateCellsEq, hinv.emptyGroupStack]
      unfold_ui_priv
      dsimp only [List.find?]
      rw [show (0 == 0) = true from rfl, ← hinv.stateCellsEq]
      dsimp only
      rw [← hinv.emptyGroupStack]
    let newSt := reduceCalculatorStateModel cSt k
    let comp2 : Compose.ComposerModel JvmVal :=
      if (Jvm.JvmVal.beqVal beqCalcExt) (.ext (.calcState cSt)) (.ext (.calcState newSt)) then
        st.heap.composer
      else
        { st.heap.composer with
          stateCells := [(0, .ext (.calcState newSt))]
          groups := st.heap.composer.groups.map fun g =>
            if 0 ∈ g.reads then { g with dirty := true } else g }
    have hwrite : Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt) st.heap.composer 0
        (.ext (.calcState newSt)) = some comp2 := by
      dsimp only [Compose.writeMutableState]
      rw [hinv.stateCellsEq]
      dsimp only [List.find?]
      rw [show (0 == 0) = true from rfl]
      cases hbeq : (Jvm.JvmVal.beqVal beqCalcExt (.ext (.calcState cSt)) (.ext (.calcState newSt))) <;>
        dsimp only [comp2] <;> simp [hbeq]
    have h30Det := CalculatorApp_lambda_3_0_equiv (depth - 1) fuel fuel (by omega) (by omega) (by omega)
      0 k cSt st.heap st.jvmHeap hinv.whenMappings st.heap.composer comp2 hread hwrite
    obtain ⟨detEnd, hdetRun, hjhDet, hhpDet⟩ := h30Det
    rw [hdetRun] at hRun30
    simp only [Option.some.injEq, Prod.mk.injEq] at hRun30
    rcases hRun30 with ⟨_, rfl⟩
    let endSt : JvmState := { st with jvmHeap := dispEndSt.jvmHeap, heap := dispEndSt.heap }
    have hEndJh : endSt.jvmHeap = st.jvmHeap := by
      dsimp only [endSt]; rw [← hjhSub, hjhDet]
    have hEndHp : endSt.heap = { st.heap with composer := comp2 } := by
      dsimp only [endSt]; rw [← hhpSub, hhpDet]
    let gApp2 : Compose.GroupEntry JvmVal :=
      if (Jvm.JvmVal.beqVal beqCalcExt) (.ext (.calcState cSt)) (.ext (.calcState newSt)) then gApp
      else if 0 ∈ gApp.reads then { gApp with dirty := true } else gApp
    let gScr2 : Compose.GroupEntry JvmVal :=
      if (Jvm.JvmVal.beqVal beqCalcExt) (.ext (.calcState cSt)) (.ext (.calcState newSt)) then gScr
      else if 0 ∈ gScr.reads then { gScr with dirty := true } else gScr
    have hgApp2Eq : gApp2.key = (54337357 : Int32) ∧
        gApp2.slots = [.ext (.stateRef 0), .ext (.closureRef cidOnKey)] ∧
        gApp2.restartClosure? = some (.ext (.closureRef appRestart)) := by
      dsimp only [gApp2]
      split
      · exact ⟨hgk, hgsl, hgrc⟩
      · split <;> exact ⟨hgk, hgsl, hgrc⟩
    have hgScr2Eq : gScr2.key = (2094116101 : Int32) ∧
        gScr2.slots = [.ext (.calcState cSt), .ext (.closureRef cidKey)] ∧
        gScr2.restartClosure? = some (.ext (.closureRef scrRestart)) := by
      dsimp only [gScr2]
      split
      · exact ⟨hsk, hssl, hsrc⟩
      · split <;> exact ⟨hsk, hssl, hsrc⟩
    have hcomp2Trace : comp2.traceEnabled = false := by
      dsimp only [comp2]; split <;> exact hinv.traceDisabled
    have hcomp2Cells : comp2.stateCells = [(0, .ext (.calcState newSt))] := by
      dsimp only [comp2]
      split
      · next hbeq =>
        have hEqSt : cSt = newSt :=
          CalcExt.calcState.inj (of_decide_eq_true (by exact hbeq))
        rw [← hEqSt]; exact hinv.stateCellsEq
      · rfl
    have hcomp2Next : comp2.nextStateId = 1 := by
      dsimp only [comp2]; split <;> exact hinv.nextStateIdEq
    have hcomp2Groups : comp2.groups = [gApp2, gScr2] := by
      dsimp only [comp2, gApp2, gScr2]
      split
      · exact hgr
      · rw [hgr]; rfl
    let compRecomp := Compose.beginRecompose endSt.heap.composer
    let hpRecomp : CalcHeap := { endSt.heap with composer := compRecomp, nodeStack := [] }
    have hRecompRoot : Compose.rootRestartClosure? compRecomp = some (.ext (.closureRef appRestart)) := by
      dsimp only [Compose.rootRestartClosure?, compRecomp, Compose.beginRecompose]
      rw [hEndHp]
      dsimp only
      rw [hcomp2Groups]
      dsimp only [List.findSome?]
      rw [hgApp2Eq.2.2]
    have hClosAppRecomp : endSt.heap.closures[appRestart]? =
        some ("CalculatorScreenKt.CalculatorApp$lambda$4",
          [.ext (.calcState .initial), .ext (.modifier none), .i32 chFlag, .i32 3]) := by
      rw [hEndHp]; exact hClosApp
    have hexpEq : expectedSt = newSt := by dsimp only [expectedSt]; rw [hmap]
    by_cases hSame : newSt = cSt
    · have hgScr2Slots' : gScr2.slots = [.ext (.calcState newSt), .ext (.closureRef cidKey)] := by
        rw [hSame]; exact hgScr2Eq.2.1
      have hgScr2Clean : gScr2.dirty = false := by
        dsimp only [gScr2]
        have hbeqTrue : (Jvm.JvmVal.beqVal beqCalcExt (.ext (.calcState cSt)) (.ext (.calcState newSt))) = true := by
          rw [hSame]; simp [Jvm.JvmVal.beqVal, beqCalcExt]
        simp [hbeqTrue, hsd]
      have hRootRecomp : hpRecomp.emittedRoot? = some (calculatorScreenMosaicNode newSt cidKey) := by
        dsimp only [hpRecomp]
        rw [hEndHp, hSame]
        exact hroot
      have hLam4 := CalculatorApp_lambda_4_skip_equiv depth fuel fuel (by omega) (by omega) (by omega)
        .initial newSt chFlag 0 hch cidOnKey cidKey hpRecomp endSt.jvmHeap
        (by rfl) (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Trace)
        (by rfl) (by rfl)
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Cells)
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Next)
        hRootRecomp
        gApp2 gScr2
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Groups)
        hgApp2Eq.1 hgApp2Eq.2.1 hgScr2Eq.1 hgScr2Slots' hgScr2Clean
        (by rw [hEndJh]; exact hinv.whenMappings)
      obtain ⟨stLam4, gApp3, gScr3, hrunLam4, hjhLam4, hclosLam4, hnsLam4, hrootLam4,
        htrLam4, hgsLam4, hcellsLam4, hnextLam4, hgrLam4, hgkLam4, hgslLam4, hgrcLam4,
        hskLam4, hsslLam4, hsdLam4, hsrcLam4⟩ := hLam4
      have hrecompEq : recomposeAppJvm calcProgLookup depth fuel endSt =
          some { endSt with jvmHeap := stLam4.jvmHeap, heap := stLam4.heap } := by
        dsimp only [recomposeAppJvm]
        rw [hRecompRoot]
        dsimp only
        rw [hClosAppRecomp]
        dsimp only
        rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$4" =
          some CalculatorApp_lambda_4_prog from rfl]
        dsimp only
        erw [hrunLam4]
      let recompSt : JvmState := { endSt with jvmHeap := stLam4.jvmHeap, heap := stLam4.heap }
      have hsingRecomp : HasSingletonRowLambdas recompSt.jvmHeap recompSt.heap.closures := by
        dsimp only [recompSt]
        rw [hjhLam4, hEndJh, hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hinv.singletonLambdas
        refine ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, ?_, ?_, ?_, ?_⟩
        · rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hc0).1]; exact hc0
        · rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hc1).1]; exact hc1
        · rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hc2).1]; exact hc2
        · rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hc3).1]; exact hc3
      have hClosOnKeyRecomp : recompSt.heap.closures[cidOnKey]? =
          some ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hClosOnKey).1]
        exact hClosOnKey
      have hClosKeyRecomp : recompSt.heap.closures[cidKey]? =
          some ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [.ext (.closureRef cidOnKey)]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        rw [array_push2_getElem?_lt _ _ _ (Array.getElem?_eq_some_iff.mp hClosKey).1]
        exact hClosKey
      have hClosAppRecomp' : recompSt.heap.closures[hpRecomp.closures.size + 1]? =
          some ("CalculatorScreenKt.CalculatorApp$lambda$4",
            [.ext (.calcState .initial), .ext (.modifier none), .i32 1, .i32 3]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        rw [show hpRecomp.closures.size + 1 =
            (hpRecomp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
              [.ext (.calcState newSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0])).size
          from by simp]
        rw [Array.getElem?_eq_getElem (by simp)]
        rw [Array.getElem_push_eq]
      have hInvNew : ValidCalculatorAppHeap newSt recompSt.jvmHeap recompSt.heap := {
        whenMappings := by dsimp only [recompSt]; rw [hjhLam4, hEndJh]; exact hinv.whenMappings
        singletonLambdas := hsingRecomp
        traceDisabled := htrLam4
        emptyNodeStack := hnsLam4
        emptyGroupStack := hgsLam4
        stateCellsEq := hcellsLam4
        nextStateIdEq := hnextLam4
        groupsShape := by
          exact ⟨gApp3, gScr3, cidOnKey, cidKey, hpRecomp.closures.size + 1,
            hpRecomp.closures.size, 1,
            hgrLam4, hgkLam4, hgslLam4, hgrcLam4, hskLam4, hsslLam4, hsdLam4, hsrcLam4,
            hClosOnKeyRecomp, hClosKeyRecomp, Or.inr rfl, hClosAppRecomp', hrootLam4⟩
      }
      refine ⟨true, endSt, calculatorScreenMosaicNode newSt cidKey, hdispEq, rfl, ?_⟩
      rw [hexpEq]
      exact ⟨recompSt, hrecompEq, hInvNew, hrootLam4, calculatorScreenMosaicNode_render newSt cidKey⟩
    · have hNe : cSt ≠ newSt := Ne.symm hSame
      have hLam4 := CalculatorApp_lambda_4_equiv depth fuel fuel (by omega) (by omega) (by omega)
        .initial newSt cSt hNe chFlag 0 hch cidOnKey cidKey hpRecomp endSt.jvmHeap
        (by rfl) (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Trace)
        (by rfl) (by rfl)
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Cells)
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Next)
        gApp2 gScr2
        (by dsimp only [hpRecomp, compRecomp, Compose.beginRecompose]; rw [hEndHp]; exact hcomp2Groups)
        hgApp2Eq.1 hgApp2Eq.2.1 hgScr2Eq.1 hgScr2Eq.2.1
        (by rw [hEndJh]; exact hinv.whenMappings)
        (by dsimp only [hpRecomp]; rw [hEndJh, hEndHp]; exact hinv.singletonLambdas)
      obtain ⟨stLam4, gApp3, gScr3, hrunLam4, hjhLam4, hclosLam4, hnsLam4, hrootLam4,
        htrLam4, hgsLam4, hcellsLam4, hnextLam4, hgrLam4, hgkLam4, hgslLam4, hgrcLam4,
        hskLam4, hsslLam4, hsdLam4, hsrcLam4⟩ := hLam4
      have hrecompEq : recomposeAppJvm calcProgLookup depth fuel endSt =
          some { endSt with jvmHeap := stLam4.jvmHeap, heap := stLam4.heap } := by
        dsimp only [recomposeAppJvm]
        rw [hRecompRoot]
        dsimp only
        rw [hClosAppRecomp]
        dsimp only
        rw [show calcProgLookup "CalculatorScreenKt.CalculatorApp$lambda$4" =
          some CalculatorApp_lambda_4_prog from rfl]
        dsimp only
        erw [hrunLam4]
      let recompSt : JvmState := { endSt with jvmHeap := stLam4.jvmHeap, heap := stLam4.heap }
      have hsingRecomp : HasSingletonRowLambdas recompSt.jvmHeap recompSt.heap.closures := by
        dsimp only [recompSt]
        rw [hjhLam4, hEndJh, hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        obtain ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, hc0, hc1, hc2, hc3⟩ := hinv.singletonLambdas
        refine ⟨id0, id1, id2, id3, hs0, hs1, hs2, hs3, ?_, ?_, ?_, ?_⟩
        · rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hc0).1]; exact hc0
        · rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hc1).1]; exact hc1
        · rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hc2).1]; exact hc2
        · rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hc3).1]; exact hc3
      have hClosOnKeyRecomp : recompSt.heap.closures[cidOnKey]? =
          some ("CalculatorScreenKt.CalculatorApp$lambda$3$0", [.ext (.stateRef 0)]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hClosOnKey).1]
        exact hClosOnKey
      have hClosKeyRecomp : recompSt.heap.closures[cidKey]? =
          some ("CalculatorScreenKt.CalculatorScreen$lambda$0$0", [.ext (.closureRef cidOnKey)]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        dsimp only [hpRecomp]
        rw [hEndHp]
        rw [array_push3_getElem?_lt _ _ _ _ (Array.getElem?_eq_some_iff.mp hClosKey).1]
        exact hClosKey
      have hClosAppRecomp' : recompSt.heap.closures[hpRecomp.closures.size + 1 + 1]? =
          some ("CalculatorScreenKt.CalculatorApp$lambda$4",
            [.ext (.calcState .initial), .ext (.modifier none), .i32 1, .i32 3]) := by
        dsimp only [recompSt]
        rw [hclosLam4]
        rw [show hpRecomp.closures.size + 1 + 1 =
            ((hpRecomp.closures.push ("CalculatorScreenKt.CalculatorScreen$lambda$1",
              [.ext (.calcState newSt)])).push ("CalculatorScreenKt.CalculatorScreen$lambda$2",
              [.ext (.calcState newSt), .ext (.closureRef cidOnKey), .ext (.modifier none), .i32 432, .i32 0])).size
          from by simp [Nat.add_assoc]]
        rw [Array.getElem?_eq_getElem (by simp)]
        rw [Array.getElem_push_eq]
      have hInvNew : ValidCalculatorAppHeap newSt recompSt.jvmHeap recompSt.heap := {
        whenMappings := by dsimp only [recompSt]; rw [hjhLam4, hEndJh]; exact hinv.whenMappings
        singletonLambdas := hsingRecomp
        traceDisabled := htrLam4
        emptyNodeStack := hnsLam4
        emptyGroupStack := hgsLam4
        stateCellsEq := hcellsLam4
        nextStateIdEq := hnextLam4
        groupsShape := by
          exact ⟨gApp3, gScr3, cidOnKey, cidKey, hpRecomp.closures.size + 1 + 1,
            hpRecomp.closures.size + 1, 1,
            hgrLam4, hgkLam4, hgslLam4, hgrcLam4, hskLam4, hsslLam4, hsdLam4, hsrcLam4,
            hClosOnKeyRecomp, hClosKeyRecomp, Or.inr rfl, hClosAppRecomp', hrootLam4⟩
      }
      refine ⟨true, endSt, calculatorScreenMosaicNode newSt cidKey, hdispEq, rfl, ?_⟩
      rw [hexpEq]
      exact ⟨recompSt, hrecompEq, hInvNew, hrootLam4, calculatorScreenMosaicNode_render newSt cidKey⟩

/-- Execute one terminal key event (and recompose if handled) under JVM + Compose + Mosaic semantics. -/
def stepUiKeyJvm (depth fuel : Nat) (st : JvmState) (keyStr : String) : Option JvmState :=
  match dispatchKeyEventJvm calcProgLookup depth fuel keyStr st with
  | some (true, endSt) => recomposeAppJvm calcProgLookup depth fuel endSt
  | some (false, endSt) => some endSt
  | none => none

/-- Fold `stepUiKeyJvm` over a sequence of terminal keystrokes. -/
def runUiKeysJvm (depth fuel : Nat) (st : JvmState) (keys : List String) : Option JvmState :=
  keys.foldlM (stepUiKeyJvm depth fuel) st

private theorem runUiKeysJvm_preserves (depth fuel : Nat)
    (hd : 6 ≤ depth) (hf : 200 ≤ fuel)
    (keys : List String) (cSt : CalculatorState) (st : JvmState)
    (hinv : ValidCalculatorAppHeap cSt st.jvmHeap st.heap) :
    let expectedSt := keys.foldl (fun s k =>
      match mapTerminalKeyModel k with
      | some ck => reduceCalculatorStateModel s ck
      | none => s) cSt
    ∃ finalSt tree,
      runUiKeysJvm depth fuel st keys = some finalSt ∧
      ValidCalculatorAppHeap expectedSt finalSt.jvmHeap finalSt.heap ∧
      finalSt.heap.emittedRoot? = some tree ∧
      Mosaic.renderMosaic tree = expectedCalculatorScreen expectedSt := by
  induction keys generalizing cSt st with
  | nil =>
    obtain ⟨tree, hroot, hrend⟩ := hinv.renders_expected
    exact ⟨st, tree, rfl, hinv, hroot, hrend⟩
  | cons k ks ih =>
    have hstep := CalculatorApp_dispatchKeyEvent_and_recompose depth fuel hd hf cSt k st hinv
    obtain ⟨handled, dispSt, _, hdisp, hhand, hpost⟩ := hstep
    cases hmap : mapTerminalKeyModel k with
    | none =>
      rw [hmap] at hhand hpost
      have hfalse : handled = false := hhand
      subst hfalse
      have hstepEq : stepUiKeyJvm depth fuel st k = some dispSt := by
        dsimp only [stepUiKeyJvm]; rw [hdisp]
      have hfold : List.foldl (fun s k => match mapTerminalKeyModel k with
          | some ck => reduceCalculatorStateModel s ck | none => s) cSt (k :: ks) =
          List.foldl (fun s k => match mapTerminalKeyModel k with
          | some ck => reduceCalculatorStateModel s ck | none => s) cSt ks := by
        dsimp only [List.foldl]; rw [hmap]
      rcases hpost with ⟨hinv', _, _⟩
      have hrec := ih cSt dispSt hinv'
      obtain ⟨finalSt, tree, hrun, hinvF, hrootF, hrendF⟩ := hrec
      dsimp only [runUiKeysJvm, List.foldlM]
      rw [hstepEq]
      dsimp only [bind, Option.bind]
      rw [hfold]
      exact ⟨finalSt, tree, hrun, hinvF, hrootF, hrendF⟩
    | some ck =>
      rw [hmap] at hhand hpost
      have htrue : handled = true := hhand
      subst htrue
      obtain ⟨recompSt, hrecomp, hinv', _, _⟩ := hpost
      have hstepEq : stepUiKeyJvm depth fuel st k = some recompSt := by
        dsimp only [stepUiKeyJvm]; rw [hdisp]; dsimp only; exact hrecomp
      have hfold : List.foldl (fun s k => match mapTerminalKeyModel k with
          | some ck => reduceCalculatorStateModel s ck | none => s) cSt (k :: ks) =
          List.foldl (fun s k => match mapTerminalKeyModel k with
          | some ck => reduceCalculatorStateModel s ck | none => s)
            (reduceCalculatorStateModel cSt ck) ks := by
        dsimp only [List.foldl]; rw [hmap]
      have hrec := ih (reduceCalculatorStateModel cSt ck) recompSt hinv'
      obtain ⟨finalSt, tree, hrun, hinvF, hrootF, hrendF⟩ := hrec
      dsimp only [runUiKeysJvm, List.foldlM]
      rw [hstepEq]
      dsimp only [bind, Option.bind]
      rw [hfold]
      exact ⟨finalSt, tree, hrun, hinvF, hrootF, hrendF⟩

/-- End-to-end terminal calculator UI theorem: starting from initial bytecode composition of
`CalculatorApp`, executing any sequence of terminal key events updates the snapshot `MutableState`,
recomposes the Compose tree, and renders the exact `expectedCalculatorScreen`. -/
theorem CalculatorApp_runKeys_renders_expected (depth fuel : Nat)
    (hd : 6 ≤ depth) (hf : 200 ≤ fuel) (keys : List String) :
    let expectedSt := keys.foldl (fun s k =>
      match mapTerminalKeyModel k with
      | some ck => reduceCalculatorStateModel s ck
      | none => s) .initial
    ∃ initSt finalSt tree,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup depth fuel) fuel CalculatorApp_prog
          (initCalcJvmState [(0, .null), (1, .null), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
            { closures := calcUiInitClosures } calcUiInitJvmHeap) =
        some (.unit, initSt) ∧
      runUiKeysJvm depth fuel initSt keys = some finalSt ∧
      ValidCalculatorAppHeap expectedSt finalSt.jvmHeap finalSt.heap ∧
      finalSt.heap.emittedRoot? = some tree ∧
      Mosaic.renderMosaic tree = expectedCalculatorScreen expectedSt := by
  obtain ⟨initSt, _, hinitRun, hinitInv, _, _⟩ :=
    CalculatorApp_initial_renders_expected depth fuel fuel (by omega) (by omega) hf
  obtain ⟨finalSt, tree, hrunKeys, hinvF, hrootF, hrendF⟩ :=
    runUiKeysJvm_preserves depth fuel hd hf keys .initial initSt hinitInv
  exact ⟨initSt, finalSt, tree, hinitRun, hrunKeys, hinvF, hrootF, hrendF⟩

/-- Bytecode equivalence theorem for `ComposableSingletons$CalculatorScreenKt.<init>()V`. -/
theorem com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_equiv
    (d f : Nat) (hd : 1 ≤ d) (hf : 5 ≤ f) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt) (cls : String) :
    ∃ endSt,
      Jvm.runJvmRes (mkCalcHooks calcProgLookup d f) f
          com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_prog
          (initCalcJvmState [(0, .allocRef cls)] hp jh) =
        some (.unit, endSt) ∧
      endSt.jvmHeap = jh ∧
      endSt.heap = hp := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hd
  obtain ⟨kF, rfl⟩ := Nat.exists_eq_add_of_le' hf
  have hloc : @setLocal CalcExt (fun _ => .i32 0) 0 (.allocRef cls) 0 = .allocRef cls := rfl
  have hs : Jvm.stepInstr (mkCalcHooks calcProgLookup (d' + 1) (kF + 5))
      (.invokespecial "java/lang/Object" "<init>" "()V")
      ⟨1, [.allocRef cls], setLocal (fun _ => .i32 0) 0 (.allocRef cls), jh, hp⟩ =
      .inl (some ⟨2, [], setLocal (fun _ => .i32 0) 0 (.allocRef cls), jh, hp⟩) := by
    dsimp only [Jvm.stepInstr, mkCalcHooks]
    unfold_ui_priv
    rfl
  have hFast :
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d' + 1) (kF + 5)) (kF + 5)
          com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_prog 0
          com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_prog
          (initCalcJvmState [(0, .allocRef cls)] hp jh) =
        some (.unit, ⟨2, [], setLocal (fun _ => .i32 0) 0 (.allocRef cls), jh, hp⟩) := by
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl,
      com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_prog]
    rw [runFast_aload, hloc]
    rw [Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d' + 1) (kF + 5)) rfl (by simp) hs rfl]
    exact runFast_vreturn'
  exact ⟨_, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl hFast, rfl, rfl⟩

end MosaicCalculator.KotlinJvmVerification

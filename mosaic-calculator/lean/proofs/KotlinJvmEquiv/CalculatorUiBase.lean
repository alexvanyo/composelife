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

import Jvm.FastExec
import Jvm.Proofs
import Jvm.Tactics
import JvmSemantics
import KotlinJvmBytecode
import models.CalculatorModel

namespace MosaicCalculator.KotlinJvmVerification

open MosaicCalculator.JvmVerification
open MosaicCalculator.KotlinJvmBytecode
open MosaicCalculator.Model

/-- Complete program table resolving all lifted methods in `CalculatorEngineKt`, `CalculatorScreenKt`, and
`ComposableSingletons$CalculatorScreenKt`. -/
def calcProgLookup : String → Option (List JvmInstr)
  | "CalculatorEngineKt.checkedAdd" => some checkedAdd_prog
  | "CalculatorEngineKt.checkedSub" => some checkedSub_prog
  | "CalculatorEngineKt.checkedMul" => some checkedMul_prog
  | "CalculatorEngineKt.checkedDiv" => some checkedDiv_prog
  | "CalculatorEngineKt.applyOp" => some applyOp_prog
  | "CalculatorEngineKt.reduceCalculatorState" => some reduceCalculatorState_prog
  | "CalculatorEngineKt.mapTerminalKey" => some mapTerminalKey_prog
  | "CalculatorEngineKt.formatDisplayLine" => some formatDisplayLine_prog
  | "CalculatorScreenKt.CalculatorApp" => some CalculatorApp_prog
  | "CalculatorScreenKt.CalculatorScreen" => some CalculatorScreen_prog
  | "CalculatorScreenKt.CalculatorApp$lambda$1" => some CalculatorApp_lambda_1_prog
  | "CalculatorScreenKt.CalculatorApp$lambda$2" => some CalculatorApp_lambda_2_prog
  | "CalculatorScreenKt.CalculatorApp$lambda$3$0" => some CalculatorApp_lambda_3_0_prog
  | "CalculatorScreenKt.CalculatorApp$lambda$4" => some CalculatorApp_lambda_4_prog
  | "CalculatorScreenKt.CalculatorScreen$lambda$0$0" => some CalculatorScreen_lambda_0_0_prog
  | "CalculatorScreenKt.CalculatorScreen$lambda$1" => some CalculatorScreen_lambda_1_prog
  | "CalculatorScreenKt.CalculatorScreen$lambda$2" => some CalculatorScreen_lambda_2_prog
  | "ComposableSingletons$CalculatorScreenKt.<init>" =>
    some com_alexvanyo_composelife_mosaiccalculator_ComposableSingletons_CalculatorScreenKt_prog
  | "ComposableSingletons$CalculatorScreenKt.getLambda$125313259$ComposeLife_mosaic_calculator" =>
    some getLambda_125313259_ComposeLife_mosaic_calculator_prog
  | "ComposableSingletons$CalculatorScreenKt.getLambda$9509460$ComposeLife_mosaic_calculator" =>
    some getLambda_9509460_ComposeLife_mosaic_calculator_prog
  | "ComposableSingletons$CalculatorScreenKt.getLambda$2033009011$ComposeLife_mosaic_calculator" =>
    some getLambda_2033009011_ComposeLife_mosaic_calculator_prog
  | "ComposableSingletons$CalculatorScreenKt.getLambda$-238458734$ComposeLife_mosaic_calculator" =>
    some getLambda__238458734_ComposeLife_mosaic_calculator_prog
  | "ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0" =>
    some lambda_125313259_lambda_0_prog
  | "ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0" =>
    some lambda_9509460_lambda_0_prog
  | "ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0" =>
    some lambda_2033009011_lambda_0_prog
  | "ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0" =>
    some lambda__238458734_lambda_0_prog
  | "ComposableSingletons$CalculatorScreenKt.<clinit>" =>
    some clinit_ComposableSingletons_CalculatorScreenKt_prog
  | _ => none

/-- Full recursive JVM hooks for UI + engine execution (`depth := 8`, `fuel := 500`). -/
def uiHooks : Jvm.JvmHooks CalcExt CalcHeap :=
  mkCalcHooks calcProgLookup 8 500

private instance mkCalcHooks_hasDefaultIsZero (r : String → Option (List JvmInstr)) (d f : Nat) :
    Jvm.HasDefaultIsZero (mkCalcHooks r d f) := by
  cases d <;> exact ⟨rfl⟩

/-- Predicate asserting `ComposableSingletons$CalculatorScreenKt` static row lambdas are initialized. -/
def HasSingletonRowLambdas (jh : Jvm.JvmHeap CalcExt) (closures : Array (String × List JvmVal)) : Prop :=
  ∃ id0 id1 id2 id3,
    jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$125313259" =
      some (.ext (.closureRef id0)) ∧
    jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$9509460" =
      some (.ext (.closureRef id1)) ∧
    jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$2033009011" =
      some (.ext (.closureRef id2)) ∧
    jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$-238458734" =
      some (.ext (.closureRef id3)) ∧
    closures[id0]? = some ("ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0", []) ∧
    closures[id1]? = some ("ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0", []) ∧
    closures[id2]? = some ("ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0", []) ∧
    closures[id3]? = some ("ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0", [])

/-- Default stop predicate pausing chunked fast-execution at calls, allocations, field accesses, casts, and heap ops. -/
def isUiStop : JvmInstr → Bool
  | .invokestatic _ _ _ => true
  | .invokevirtual _ _ _ => true
  | .invokeinterface _ _ _ => true
  | .invokespecial _ _ _ => true
  | .invokedynamic _ _ _ => true
  | .getstatic _ _ _ => true
  | .putstatic _ _ _ => true
  | .newClass _ => true
  | .iaload => true
  | .checkcast _ => true
  | .instanceof _ => true
  | _ => false

theorem uiHooks_chunk {hooks : Jvm.JvmHooks CalcExt CalcHeap} (maxSteps fuel : Nat)
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    Jvm.runJvmResFast hooks fuel prog pc instrs st =
      Jvm.afterResBlockChunk hooks (Jvm.stepResBlockChunkWith hooks isUiStop maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmResFast_stepBlockChunkWith hooks isUiStop maxSteps fuel prog pc instrs st

theorem runFast_dup {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.dup :: rest) ⟨pc, v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, v :: v :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_iconst {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {n : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iconst n :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 n :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

private theorem exec_singleton_getLambda {d f : Nat} (fld : String) (v : JvmVal)
    (hp : CalcHeap) {jh : Jvm.JvmHeap CalcExt}
    (hgs : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" fld = some v) :
    Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 10
        [.getstatic "ComposableSingletons$CalculatorScreenKt" fld "Lkotlin/jvm/functions/Function3;", .areturn]
        (initCalcJvmState [] hp jh) =
      some (v, { pc := 1, stack := [v], locals := fun _ => .i32 0, jvmHeap := jh, heap := hp }) := by
  apply Jvm.runJvmRes_of_runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) 10 _ 0 _ _ _ rfl rfl
  have h1 : Jvm.stepInstr (mkCalcHooks calcProgLookup (d + 1) f)
      (.getstatic "ComposableSingletons$CalculatorScreenKt" fld "Lkotlin/jvm/functions/Function3;")
      ⟨0, [], fun _ => .i32 0, jh, hp⟩ =
      .inl (some ⟨1, [v], fun _ => .i32 0, jh, hp⟩) := by
    dsimp [Jvm.stepInstr]
    rw [hgs]
  dsimp only [initCalcJvmState, Jvm.initJvmState, List.drop, List.foldl]
  rw [Jvm.runJvmResFast_step_of_stepInstr (mkCalcHooks calcProgLookup (d + 1) f) rfl (by simp) h1 rfl]
  rfl

theorem getLambda_125313259_bytecode_equiv (d f : Nat) (hp : CalcHeap) {jh : Jvm.JvmHeap CalcExt} {v : JvmVal}
    (hgs : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$125313259" = some v) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 10
        getLambda_125313259_ComposeLife_mosaic_calculator_prog (initCalcJvmState [] hp jh) =
        some (v, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hp :=
  ⟨_, exec_singleton_getLambda "lambda$125313259" v hp hgs, rfl, rfl⟩

theorem getLambda_9509460_bytecode_equiv (d f : Nat) (hp : CalcHeap) {jh : Jvm.JvmHeap CalcExt} {v : JvmVal}
    (hgs : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$9509460" = some v) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 10
        getLambda_9509460_ComposeLife_mosaic_calculator_prog (initCalcJvmState [] hp jh) =
        some (v, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hp :=
  ⟨_, exec_singleton_getLambda "lambda$9509460" v hp hgs, rfl, rfl⟩

theorem getLambda_2033009011_bytecode_equiv (d f : Nat) (hp : CalcHeap) {jh : Jvm.JvmHeap CalcExt} {v : JvmVal}
    (hgs : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$2033009011" = some v) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 10
        getLambda_2033009011_ComposeLife_mosaic_calculator_prog (initCalcJvmState [] hp jh) =
        some (v, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hp :=
  ⟨_, exec_singleton_getLambda "lambda$2033009011" v hp hgs, rfl, rfl⟩

theorem getLambda__238458734_bytecode_equiv (d f : Nat) (hp : CalcHeap) {jh : Jvm.JvmHeap CalcExt} {v : JvmVal}
    (hgs : jh.getStatic? "ComposableSingletons$CalculatorScreenKt" "lambda$-238458734" = some v) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 10
        getLambda__238458734_ComposeLife_mosaic_calculator_prog (initCalcJvmState [] hp jh) =
        some (v, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hp :=
  ⟨_, exec_singleton_getLambda "lambda$-238458734" v hp hgs, rfl, rfl⟩

private theorem runFast_newClass {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {cls : String} {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnsb : (cls == "java/lang/StringBuilder") = false) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc (.newClass cls :: rest)
        ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .allocRef cls :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, mkCalcHooks]
  simp [hnsb]

private theorem runFast_invokespecial_singletonInit {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {c1 c2 : String} {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokespecial "ComposableSingletons$CalculatorScreenKt" "<init>" "()V" :: rest)
        ⟨pc, .allocRef c1 :: .allocRef c2 :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.companion "ComposableSingletons$CalculatorScreenKt") :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeSpecialGeneric, mkCalcHooks]
  rfl

private theorem runFast_putstatic {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {cls fld desc : String} {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.putstatic cls fld desc :: rest) ⟨pc, v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh.setStatic cls fld v, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) rfl rfl

private theorem runFast_checkcast_fn3 {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {cid : Nat} {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.checkcast "kotlin/jvm/functions/Function3" :: rest)
        ⟨pc, .ext (.closureRef cid) :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef cid) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.evalCheckCast, mkCalcHooks]
  rfl

private theorem runFast_composableLambdaInstance {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {key tracked block : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/internal/ComposableLambdaKt" "composableLambdaInstance"
          "(IZLjava/lang/Object;)Landroidx/compose/runtime/internal/ComposableLambda;" :: rest)
        ⟨pc, block :: tracked :: key :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, block :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

private theorem runFast_lambda0 {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {bsmArg fnTag : String} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hex : extractBsmTarget bsmArg = some fnTag) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokedynamic "LambdaMetafactory" bsmArg "()Lkotlin/jvm/functions/Function3;" :: rest)
        ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.closureRef hp.closures.size) :: stack, locs, jh, (allocClosure hp fnTag []).2⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  have htags : (Jvm.parseMethodParamTags "()Lkotlin/jvm/functions/Function3;").length = 0 := rfl
  have hbsm : ("LambdaMetafactory" == "makeConcatWithConstants") = false := rfl
  have hlbm : ("LambdaMetafactory" == "LambdaMetafactory") = true := rfl
  dsimp only [Jvm.stepInstr, mkCalcHooks]
  rw [hbsm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hlbm]
  simp only [↓reduceIte, htags, hex, Nat.not_lt_zero, List.take_zero, List.drop_zero, List.reverse_nil]
  rfl

private theorem bsm_lambda_125313259 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0" := by
  set_option maxRecDepth 2048 in rfl

private theorem bsm_lambda_9509460 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0" := by
  set_option maxRecDepth 2048 in rfl

private theorem bsm_lambda_2033009011 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0" := by
  set_option maxRecDepth 2048 in rfl

private theorem bsm_lambda_238458734 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0:(Lcom/jakewharton/mosaic/ui/RowScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0" := by
  set_option maxRecDepth 2048 in rfl

/-- Executing `ComposableSingletons$CalculatorScreenKt.<clinit>` initializes all 4 singleton row lambdas. -/
theorem clinit_ComposableSingletons_equiv (d f : Nat) :
    let hooks := mkCalcHooks calcProgLookup (d + 1) f
    ∃ st',
      Jvm.runJvmRes hooks 64 clinit_ComposableSingletons_CalculatorScreenKt_prog
        (initCalcJvmState [] {} calcInitJvmHeap) = some (.unit, st') ∧
      HasSingletonRowLambdas st'.jvmHeap st'.heap.closures ∧
      st'.heap.composer = {} ∧
      st'.heap.nodeStack = [] ∧
      st'.heap.emittedRoot? = none := by
  intro hooks
  have hrun : ∃ st',
      Jvm.runJvmRes hooks 64 clinit_ComposableSingletons_CalculatorScreenKt_prog
        (initCalcJvmState [] {} calcInitJvmHeap) = some (.unit, st') ∧
      st' = {
        pc := 28
        stack := []
        locals := fun _ => .i32 0
        jvmHeap := ((((calcInitJvmHeap.setStatic "ComposableSingletons$CalculatorScreenKt" "INSTANCE"
            (.ext (.companion "ComposableSingletons$CalculatorScreenKt")))
          |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$125313259" (.ext (.closureRef 0)))
          |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$9509460" (.ext (.closureRef 1)))
          |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$2033009011" (.ext (.closureRef 2)))
          |>.setStatic "ComposableSingletons$CalculatorScreenKt" "lambda$-238458734" (.ext (.closureRef 3))
        heap := {
          closures := #[
            ("ComposableSingletons$CalculatorScreenKt.lambda_125313259$lambda$0", []),
            ("ComposableSingletons$CalculatorScreenKt.lambda_9509460$lambda$0", []),
            ("ComposableSingletons$CalculatorScreenKt.lambda_2033009011$lambda$0", []),
            ("ComposableSingletons$CalculatorScreenKt.lambda__238458734$lambda$0", [])
          ]
        }
      } := by
    refine ⟨_, ?_, rfl⟩
    apply Jvm.runJvmRes_of_runJvmResFast hooks 64 _ 0 _ _ _ rfl rfl
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl, clinit_ComposableSingletons_CalculatorScreenKt_prog, List.drop]
    rw [runFast_newClass (by decide)]
    rw [runFast_dup]
    rw [runFast_invokespecial_singletonInit]
    rw [runFast_putstatic]
    rw [runFast_iconst, runFast_iconst, runFast_lambda0 bsm_lambda_125313259]
    rw [runFast_composableLambdaInstance, runFast_checkcast_fn3, runFast_putstatic]
    rw [runFast_iconst, runFast_iconst, runFast_lambda0 bsm_lambda_9509460]
    rw [runFast_composableLambdaInstance, runFast_checkcast_fn3, runFast_putstatic]
    rw [runFast_iconst, runFast_iconst, runFast_lambda0 bsm_lambda_2033009011]
    rw [runFast_composableLambdaInstance, runFast_checkcast_fn3, runFast_putstatic]
    rw [runFast_iconst, runFast_iconst, runFast_lambda0 bsm_lambda_238458734]
    rw [runFast_composableLambdaInstance, runFast_checkcast_fn3, runFast_putstatic]
    simp [allocClosure]
    rfl
  rcases hrun with ⟨st', hrun, rfl⟩
  exact ⟨_, hrun, ⟨0, 1, 2, 3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem bsm_CalculatorApp_lambda_3_0 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorApp$lambda$3$0:(Landroidx/compose/runtime/MutableState;Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorKey;)Lkotlin/Unit;" =
      some "CalculatorScreenKt.CalculatorApp$lambda$3$0" := by
  set_option maxRecDepth 4096 in rfl

theorem bsm_CalculatorApp_lambda_4 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorApp$lambda$4:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/modifier/Modifier;IILandroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "CalculatorScreenKt.CalculatorApp$lambda$4" := by
  set_option maxRecDepth 4096 in rfl

theorem bsm_CalculatorScreen_lambda_0_0 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$0$0:(Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/layout/KeyEvent;)Z" =
      some "CalculatorScreenKt.CalculatorScreen$lambda$0$0" := by
  set_option maxRecDepth 4096 in rfl

theorem bsm_CalculatorScreen_lambda_1 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$1:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lcom/jakewharton/mosaic/ui/ColumnScope;Landroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "CalculatorScreenKt.CalculatorScreen$lambda$1" := by
  set_option maxRecDepth 4096 in rfl

theorem bsm_CalculatorScreen_lambda_2 :
    extractBsmTarget
      "REF_invokeStatic com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.CalculatorScreen$lambda$2:(Lcom/alexvanyo/composelife/mosaiccalculator/CalculatorState;Lkotlin/jvm/functions/Function1;Lcom/jakewharton/mosaic/modifier/Modifier;IILandroidx/compose/runtime/Composer;I)Lkotlin/Unit;" =
      some "CalculatorScreenKt.CalculatorScreen$lambda$2" := by
  set_option maxRecDepth 4096 in rfl

theorem runFast_nop {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.nop :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_aload {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {idx : Nat} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.aload idx :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_ldcStr {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {s : String} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ldcStr s :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .str s :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_iload {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {idx : Nat} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iload idx :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_astore {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {idx : Nat} {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.astore idx :: rest) ⟨pc, v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stack, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_istore {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {idx : Nat} {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.istore idx :: rest) ⟨pc, v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stack, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_aconstNull {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.aconstNull :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .null :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_iand {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {b a : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.iand :: rest) ⟨pc, .i32 b :: .i32 a :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 (a &&& b) :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_checkNotNullParam {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {msg : JvmVal} {v : CalcExt} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
          "(Ljava/lang/Object;Ljava/lang/String;)V" :: rest)
        ⟨pc, msg :: .ext v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, Jvm.JvmVal.isNull]
  rfl

theorem runFast_sourceInfo {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {info : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformation"
          "(Landroidx/compose/runtime/Composer;Ljava/lang/String;)V" :: rest)
        ⟨pc, info :: .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_shouldExecute {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {flagsVal pVal : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z" :: rest)
        ⟨pc, .i32 flagsVal :: .i32 pVal :: .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (if Compose.shouldExecute hp.composer (pVal != 0) flagsVal.toInt32 then 1 else 0) :: stack,
          locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_isTraceInProgress {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z" :: rest)
        ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (if hp.composer.traceEnabled then 1 else 0) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_text {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {dflt ch a6 a5 a4 a3 a2 modV : JvmVal} {txt : String}
    {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "com/jakewharton/mosaic/ui/Text" "Text-cbmis8g"
          "(Ljava/lang/String;Lcom/jakewharton/mosaic/modifier/Modifier;IIIIILandroidx/compose/runtime/Composer;II)V" :: rest)
        ⟨pc, dflt :: ch :: .ext .composer :: a6 :: a5 :: a4 :: a3 :: a2 :: modV :: .str txt :: stack,
          locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, emitMosaicNode hp (.text txt)⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_getStatic_unit {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hnone : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.getstatic "kotlin/Unit" "INSTANCE" "Lkotlin/Unit;" :: rest) ⟨pc, stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext .unit :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, mkCalcHooks, normalizeCalcClass]
  rw [hnone]
  rfl

private def mkRowLambdaProg (info : String) (traceKey : UInt32) (traceInfo rowText : String) : List JvmInstr :=
  [ .aload 0, .ldcStr "$this$Row"
  , .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V"
  , .aload 1, .ldcStr info
  , .invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformation"
      "(Landroidx/compose/runtime/Composer;Ljava/lang/String;)V"
  , .aload 1, .iload 2, .iconst 17, .iand, .iconst 16, .if_icmpeq 14, .iconst 1, .goto 15, .iconst 0
  , .iload 2, .iconst 1, .iand
  , .invokeinterface "androidx/compose/runtime/Composer" "shouldExecute" "(ZI)Z"
  , .ifeq 42
  , .invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z"
  , .ifeq 27
  , .iconst traceKey, .iload 2, .iconst 4294967295, .ldcStr traceInfo
  , .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventStart" "(IIILjava/lang/String;)V"
  , .ldcStr rowText, .aconstNull, .iconst 0, .iconst 0, .iconst 0, .iconst 0, .iconst 0
  , .aload 1, .iconst 6, .iconst 126
  , .invokestatic "com/jakewharton/mosaic/ui/Text" "Text-cbmis8g"
      "(Ljava/lang/String;Lcom/jakewharton/mosaic/modifier/Modifier;IIIIILandroidx/compose/runtime/Composer;II)V"
  , .invokestatic "androidx/compose/runtime/ComposerKt" "isTraceInProgress" "()Z"
  , .ifeq 44
  , .invokestatic "androidx/compose/runtime/ComposerKt" "traceEventEnd" "()V"
  , .goto 44
  , .aload 1, .invokeinterface "androidx/compose/runtime/Composer" "skipToGroupEnd" "()V"
  , .getstatic "kotlin/Unit" "INSTANCE" "Lkotlin/Unit;"
  , .areturn ]

private theorem rowLambda_exec (d f : Nat) (info : String) (traceKey : UInt32) (traceInfo rowText : String)
    (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    let hooks := mkCalcHooks calcProgLookup (d + 1) f
    let prog := mkRowLambdaProg info traceKey traceInfo rowText
    ∃ st',
      Jvm.runJvmRes hooks 40 prog
        (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text rowText) := by
  intro hooks prog
  refine ⟨{
    pc := 45
    stack := [.ext .unit]
    locals := fun i =>
      if i = 2 then .i32 6 else if i = 1 then .ext .composer else if i = 0 then .ext .unit else .i32 0
    jvmHeap := jh
    heap := emitMosaicNode hp (.text rowText)
  }, ?_, rfl, rfl⟩
  apply Jvm.runJvmRes_of_runJvmResFast hooks 40 prog 0 prog _ _ rfl rfl
  let initLocs : Nat → JvmVal :=
    setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.ext .unit)) 1 (.ext .composer)) 2 (.i32 6)
  have hl0 : initLocs 0 = .ext .unit := rfl
  have hl1 : initLocs 1 = .ext .composer := rfl
  have hl2 : initLocs 2 = .i32 6 := rfl
  change Jvm.runJvmResFast hooks 40 prog 0 prog ⟨0, [], initLocs, jh, hp⟩ = _
  dsimp only [prog, mkRowLambdaProg]
  rw [runFast_aload, hl0, runFast_ldcStr, runFast_checkNotNullParam]
  rw [runFast_aload, hl1, runFast_ldcStr, runFast_sourceInfo]
  rw [runFast_aload, hl1, runFast_iload, hl2, runFast_iconst, runFast_iand, runFast_iconst]
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpeq]
  rw [ite_eq_right (by decide)]
  rw [runFast_iconst]
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl), Jvm.evalResBranchInstrCons_goto]
  dsimp only [List.drop]
  rw [runFast_iload, hl2, runFast_iconst, runFast_iand, runFast_shouldExecute]
  have hse : Compose.shouldExecute hp.composer (((1 : UInt32) != 0)) ((6 &&& 1 : UInt32).toInt32) = true := by
    simp [Compose.shouldExecute]
  rw [hse]
  rw [ite_eq_left (by decide)]
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
  rw [ite_eq_right (by decide)]
  rw [runFast_isTraceInProgress]
  rw [htrace]
  rw [ite_eq_right (by decide)]
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
  rw [ite_eq_left (by decide)]
  dsimp only [List.drop]
  rw [runFast_ldcStr, runFast_aconstNull, runFast_iconst, runFast_iconst, runFast_iconst,
    runFast_iconst, runFast_iconst, runFast_aload, hl1, runFast_iconst, runFast_iconst, runFast_text]
  rw [runFast_isTraceInProgress]
  have htrace' : (emitMosaicNode hp (.text rowText)).composer.traceEnabled = false := by
    dsimp [emitMosaicNode]
    cases hp.nodeStack with
    | nil => exact htrace
    | cons _ _ => exact htrace
  rw [htrace']
  rw [ite_eq_right (by decide)]
  rw [Jvm.runJvmResFast_at_branch_cons hooks (hbr := rfl), Jvm.evalResBranchInstrCons_ifeq]
  rw [ite_eq_left (by decide)]
  dsimp only [prog, mkRowLambdaProg, List.drop]
  rw [runFast_getStatic_unit hunit]
  rfl

theorem lambda_125313259_lambda_0_equiv (d f : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 40 lambda_125313259_lambda_0_prog
        (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text "[7] [8] [9] [/]") :=
  rowLambda_exec d f "C63@2157L23:CalculatorScreen.kt#b0tpbg" 125313259
    "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$125313259.<anonymous> (CalculatorScreen.kt:63)"
    "[7] [8] [9] [/]" hp jh htrace hunit

theorem lambda_9509460_lambda_0_equiv (d f : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 40 lambda_9509460_lambda_0_prog
        (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text "[4] [5] [6] [*]") :=
  rowLambda_exec d f "C66@2217L23:CalculatorScreen.kt#b0tpbg" 9509460
    "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$9509460.<anonymous> (CalculatorScreen.kt:66)"
    "[4] [5] [6] [*]" hp jh htrace hunit

theorem lambda_2033009011_lambda_0_equiv (d f : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 40 lambda_2033009011_lambda_0_prog
        (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text "[1] [2] [3] [-]") :=
  rowLambda_exec d f "C69@2277L23:CalculatorScreen.kt#b0tpbg" 2033009011
    "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$2033009011.<anonymous> (CalculatorScreen.kt:69)"
    "[1] [2] [3] [-]" hp jh htrace hunit

theorem lambda__238458734_lambda_0_equiv (d f : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (htrace : hp.composer.traceEnabled = false)
    (hunit : jh.getStatic? "kotlin/Unit" "INSTANCE" = none) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 40 lambda__238458734_lambda_0_prog
        (initCalcJvmState [(0, .ext .unit), (1, .ext .composer), (2, .i32 6)] hp jh) =
        some (.ext .unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = emitMosaicNode hp (.text "[0] [C] [=] [+]") :=
  rowLambda_exec d f "C72@2337L23:CalculatorScreen.kt#b0tpbg" 4056508562
    "com.alexvanyo.composelife.mosaiccalculator.ComposableSingletons$CalculatorScreenKt.lambda$-238458734.<anonymous> (CalculatorScreen.kt:72)"
    "[0] [C] [=] [+]" hp jh htrace hunit

theorem CalculatorApp_lambda_1_equiv (d f : Nat) (sid : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (cSt : CalculatorState) (comp' : Compose.ComposerModel JvmVal)
    (hread : Compose.readMutableState hp.composer sid = some (.ext (.calcState cSt), comp')) :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 20 CalculatorApp_lambda_1_prog
        (initCalcJvmState [(0, .ext (.stateRef sid))] hp jh) =
        some (.ext (.calcState cSt), st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
  let hooks := mkCalcHooks calcProgLookup (d + 1) f
  let locs1 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal
    (fun _ => .i32 0) 0 (.ext (.stateRef sid))) 1 (.ext (.stateRef sid))) 2 .null) 3 .null) 4 (.i32 0)
  have hrun : Jvm.runJvmRes hooks 20 CalculatorApp_lambda_1_prog
      (initCalcJvmState [(0, .ext (.stateRef sid))] hp jh) =
      some (.ext (.calcState cSt), {
        pc := 12
        stack := [.ext (.calcState cSt)]
        locals := locs1
        jvmHeap := jh
        heap := { hp with composer := comp' }
      }) := by
    apply Jvm.runJvmRes_of_runJvmResFast hooks 20 _ 0 _ _ _ rfl rfl
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl, CalculatorApp_lambda_1_prog, List.drop]
    rw [runFast_aload]; simp only [setLocal, ↓reduceIte]
    have hcc1 : Jvm.stepInstr hooks (.checkcast "androidx/compose/runtime/State")
        ⟨1, [.ext (.stateRef sid)], setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid)), jh, hp⟩ =
        .inl (some ⟨2, [.ext (.stateRef sid)], setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid)), jh, hp⟩) := by
      dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, hooks, mkCalcHooks, normalizeCalcClass]
      rfl
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hcc1 rfl]
    rw [runFast_astore, runFast_aconstNull, runFast_astore, runFast_aconstNull, runFast_astore,
      runFast_iconst, runFast_istore, runFast_aload]
    have hlocs1_1 : locs1 1 = .ext (.stateRef sid) := rfl
    change Jvm.runJvmResFast hooks 10 CalculatorApp_lambda_1_prog 10
        [.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;",
         .checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorState", .areturn]
        ⟨10, [locs1 1], locs1, jh, hp⟩ = _
    rw [hlocs1_1]
    have hget : Jvm.stepInstr hooks (.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;")
        ⟨10, [.ext (.stateRef sid)], locs1, jh, hp⟩ =
        .inl (some ⟨11, [.ext (.calcState cSt)], locs1, jh, { hp with composer := comp' }⟩) := by
      have hgen : Jvm.stepInstr hooks
          (.invokeinterface "androidx/compose/runtime/State" "getValue" "()Ljava/lang/Object;")
          ⟨10, [.ext (.stateRef sid)], locs1, jh, hp⟩ =
          match Compose.readMutableState hp.composer sid with
          | some (v, comp'') =>
            .inl (some ⟨11, [v], locs1, jh, { hp with composer := comp'' }⟩)
          | none => .inr none := rfl
      rw [hgen, hread]
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hget rfl]
    have hcc2 : Jvm.stepInstr hooks (.checkcast "com/alexvanyo/composelife/mosaiccalculator/CalculatorState")
        ⟨11, [.ext (.calcState cSt)], locs1, jh, { hp with composer := comp' }⟩ =
        .inl (some ⟨12, [.ext (.calcState cSt)], locs1, jh, { hp with composer := comp' }⟩) := by
      dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, hooks, mkCalcHooks, normalizeCalcClass]
      rfl
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hcc2 rfl]
    rfl
  exact ⟨_, hrun, rfl, rfl⟩

theorem CalculatorApp_lambda_2_equiv (d f : Nat) (sid : Nat) (hp : CalcHeap) (jh : Jvm.JvmHeap CalcExt)
    (cSt : CalculatorState) (comp' : Compose.ComposerModel JvmVal)
    (hwrite : Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt)
      hp.composer sid (.ext (.calcState cSt)) = some comp') :
    ∃ st',
      Jvm.runJvmRes (mkCalcHooks calcProgLookup (d + 1) f) 20 CalculatorApp_lambda_2_prog
        (initCalcJvmState [(0, .ext (.stateRef sid)), (1, .ext (.calcState cSt))] hp jh) =
        some (.unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = { hp with composer := comp' } := by
  let hooks := mkCalcHooks calcProgLookup (d + 1) f
  let locs2 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid)))
    1 (.ext (.calcState cSt))) 2 (.ext (.stateRef sid))) 3 .null) 4 .null) 5 (.ext (.calcState cSt))) 6 (.i32 0)
  have hrun : Jvm.runJvmRes hooks 20 CalculatorApp_lambda_2_prog
      (initCalcJvmState [(0, .ext (.stateRef sid)), (1, .ext (.calcState cSt))] hp jh) =
      some (.unit, {
        pc := 14
        stack := []
        locals := locs2
        jvmHeap := jh
        heap := { hp with composer := comp' }
      }) := by
    apply Jvm.runJvmRes_of_runJvmResFast hooks 20 _ 0 _ _ _ rfl rfl
    dsimp only [initCalcJvmState, Jvm.initJvmState, List.foldl, CalculatorApp_lambda_2_prog, List.drop]
    let initL : Nat → JvmVal :=
      setLocal (setLocal (fun _ => .i32 0) 0 (.ext (.stateRef sid))) 1 (.ext (.calcState cSt))
    have ha0 : initL 0 = .ext (.stateRef sid) := rfl
    have ha1 : (setLocal (setLocal (setLocal initL 2 (.ext (.stateRef sid))) 3 .null) 4 .null) 1 =
        .ext (.calcState cSt) := rfl
    change Jvm.runJvmResFast hooks 20 CalculatorApp_lambda_2_prog 0 CalculatorApp_lambda_2_prog
      ⟨0, [], initL, jh, hp⟩ = _
    dsimp only [CalculatorApp_lambda_2_prog]
    rw [runFast_aload, ha0, runFast_astore, runFast_aconstNull, runFast_astore, runFast_aconstNull,
      runFast_astore, runFast_aload, ha1, runFast_astore, runFast_iconst, runFast_istore,
      runFast_aload, runFast_aload]
    have h2 : locs2 2 = .ext (.stateRef sid) := rfl
    have h5 : locs2 5 = .ext (.calcState cSt) := rfl
    change Jvm.runJvmResFast hooks 8 CalculatorApp_lambda_2_prog 12
        [.invokeinterface "androidx/compose/runtime/MutableState" "setValue" "(Ljava/lang/Object;)V",
         .nop, .vreturn]
        ⟨12, [locs2 5, locs2 2], locs2, jh, hp⟩ = _
    rw [h5, h2]
    have hset : Jvm.stepInstr hooks
        (.invokeinterface "androidx/compose/runtime/MutableState" "setValue" "(Ljava/lang/Object;)V")
        ⟨12, [.ext (.calcState cSt), .ext (.stateRef sid)], locs2, jh, hp⟩ =
        .inl (some ⟨13, [], locs2, jh, { hp with composer := comp' }⟩) := by
      have hgen : Jvm.stepInstr hooks
          (.invokeinterface "androidx/compose/runtime/MutableState" "setValue" "(Ljava/lang/Object;)V")
          ⟨12, [.ext (.calcState cSt), .ext (.stateRef sid)], locs2, jh, hp⟩ =
          match Compose.writeMutableState (Jvm.JvmVal.beqVal beqCalcExt)
              hp.composer sid (.ext (.calcState cSt)) with
          | some comp'' => .inl (some ⟨13, [], locs2, jh, { hp with composer := comp'' }⟩)
          | none => .inr none := rfl
      rw [hgen, hwrite]
    rw [Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) hset rfl]
    rw [runFast_nop]
    rfl
  exact ⟨_, hrun, rfl, rfl⟩

theorem runFast_ior {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {b a : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ior :: rest) ⟨pc, .i32 b :: .i32 a :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 (a ||| b) :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_ishl {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {b a : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.ishl :: rest) ⟨pc, .i32 b :: .i32 a :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, .i32 (a <<< (b &&& 31)) :: stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_swap {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {b a : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hb : b.isCat2 = false := by rfl) (ha : a.isCat2 = false := by rfl) :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.swap :: rest) ⟨pc, b :: a :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, a :: b :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr]
  simp [hb, ha]

theorem runFast_pop {hooks : Jvm.JvmHooks CalcExt CalcHeap} {f pc : Nat}
    {prog rest : List JvmInstr} {a : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast hooks (f + 1) prog pc (.pop :: rest) ⟨pc, a :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast hooks f prog (pc + 1) rest ⟨pc + 1, stack, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr hooks rfl (by simp) rfl rfl

theorem runFast_if_acmpne_ext {d f fuel pc target : Nat} {prog rest : List JvmInstr}
    {b a : CalcExt} {eq : Bool} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (h : beqRefCalcExt a b = some eq) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup d f) (fuel + 1) prog pc (.if_acmpne target :: rest)
        ⟨pc, .ext b :: .ext a :: stack, locs, jh, hp⟩ =
      if !eq then
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup d f) fuel prog target (prog.drop target) ⟨target, stack, locs, jh, hp⟩
      else
        Jvm.runJvmResFast (mkCalcHooks calcProgLookup d f) fuel prog (pc + 1) rest ⟨pc + 1, stack, locs, jh, hp⟩ := by
  have hbeq : (mkCalcHooks calcProgLookup d f).beqRefExt = beqRefCalcExt := by cases d <;> rfl
  rw [Jvm.runJvmResFast_at_branch_cons _ (hbr := rfl)]
  dsimp [Jvm.evalResBranchInstrCons, Jvm.isBranchInstr, Jvm.dispatchBranch, Jvm.JvmVal.refEq?]
  rw [hbeq, h]
  cases eq <;> simp

theorem runFast_checkCast_ext {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {cls : String} {v : CalcExt} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap}
    (hcc : (mkCalcHooks calcProgLookup (d + 1) f).checkCast cls (.ext v) = some (.ext v)) :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.checkcast cls :: rest) ⟨pc, .ext v :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext v :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.evalCheckCast]
  rw [hcc]

theorem runFast_sourceInfoMarkerStart {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {key info : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerStart"
          "(Landroidx/compose/runtime/Composer;ILjava/lang/String;)V" :: rest)
        ⟨pc, info :: key :: .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_sourceInfoMarkerEnd {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/ComposerKt" "sourceInformationMarkerEnd"
          "(Landroidx/compose/runtime/Composer;)V" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_startRestartGroup {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {keyVal : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "startRestartGroup"
          "(I)Landroidx/compose/runtime/Composer;" :: rest)
        ⟨pc, .i32 keyVal :: .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext .composer :: stack, locs, jh,
          { hp with composer := Compose.startRestartGroup hp.composer keyVal.toInt32 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_startDefaults {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "startDefaults" "()V" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, { hp with composer := Compose.startDefaults hp.composer }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_getDefaultsInvalid {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "getDefaultsInvalid" "()Z" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (if Compose.getDefaultsInvalid hp.composer then 1 else 0) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_endDefaults {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "endDefaults" "()V" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, { hp with composer := Compose.endDefaults hp.composer }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_skipToGroupEnd {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "skipToGroupEnd" "()V" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, { hp with composer := Compose.skipToGroupEnd hp.composer }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_endRestartGroup {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "endRestartGroup"
          "()Landroidx/compose/runtime/ScopeUpdateScope;" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      let r := Compose.endRestartGroup hp.composer
      let scopeVal : JvmVal := match r.1 with | some k => .ext (.scopeUpdateScope k) | none => .null
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, scopeVal :: stack, locs, jh, { hp with composer := r.2 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_composerChanged {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "changed" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc, v :: .ext .composer :: stack, locs, jh, hp⟩ =
      let r := Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) hp.composer v
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (if r.1 then 1 else 0) :: stack, locs, jh, { hp with composer := r.2 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_composerChangedInstance {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "changedInstance" "(Ljava/lang/Object;)Z" :: rest)
        ⟨pc, v :: .ext .composer :: stack, locs, jh, hp⟩ =
      let r := Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqCalcExt) hp.composer v
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (if r.1 then 1 else 0) :: stack, locs, jh, { hp with composer := r.2 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_rememberedValue {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {stack : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "rememberedValue" "()Ljava/lang/Object;" :: rest)
        ⟨pc, .ext .composer :: stack, locs, jh, hp⟩ =
      let r := Compose.readRememberSlot hp.composer
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, r.1.getD (.ext .composerEmpty) :: stack, locs, jh, { hp with composer := r.2 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_updateRememberedValue {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/Composer" "updateRememberedValue"
          "(Ljava/lang/Object;)V" :: rest)
        ⟨pc, v :: .ext .composer :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh, { hp with composer := Compose.writeRememberSlot hp.composer v }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_updateScope {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {closureVal : JvmVal} {gk : Int32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokeinterface "androidx/compose/runtime/ScopeUpdateScope" "updateScope"
          "(Lkotlin/jvm/functions/Function2;)V" :: rest)
        ⟨pc, closureVal :: .ext (.scopeUpdateScope gk) :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, stack, locs, jh,
          { hp with composer := Compose.setGroupRestartClosure hp.composer gk closureVal }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp only [Jvm.stepInstr, Jvm.stepInvokeInterfaceGeneric, mkCalcHooks]
  rfl

theorem runFast_mutableStateOfDefault {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {marker mask policy initial : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/SnapshotStateKt" "mutableStateOf$default"
          "(Ljava/lang/Object;Landroidx/compose/runtime/SnapshotMutationPolicy;ILjava/lang/Object;)Landroidx/compose/runtime/MutableState;" :: rest)
        ⟨pc, marker :: mask :: policy :: initial :: stack, locs, jh, hp⟩ =
      let r := Compose.allocMutableState hp.composer initial
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.stateRef r.1) :: stack, locs, jh, { hp with composer := r.2 }⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_rememberComposableLambda {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {ch block tracked key : JvmVal} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/internal/ComposableLambdaKt" "rememberComposableLambda"
          "(IZLjava/lang/Object;Landroidx/compose/runtime/Composer;I)Landroidx/compose/runtime/internal/ComposableLambda;" :: rest)
        ⟨pc, ch :: .ext .composer :: block :: tracked :: key :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, block :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_onKeyEvent {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {cid : Nat} {prevH? : Option Nat} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "com/jakewharton/mosaic/layout/KeyModifierKt" "onKeyEvent"
          "(Lcom/jakewharton/mosaic/modifier/Modifier;Lkotlin/jvm/functions/Function1;)Lcom/jakewharton/mosaic/modifier/Modifier;" :: rest)
        ⟨pc, .ext (.closureRef cid) :: .ext (.modifier prevH?) :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.modifier (some cid)) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_updateChangedFlags {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {flagsVal : UInt32} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokestatic "androidx/compose/runtime/RecomposeScopeImplKt" "updateChangedFlags" "(I)I" :: rest)
        ⟨pc, .i32 flagsVal :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .i32 (Compose.updateChangedFlags flagsVal) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  dsimp [Jvm.stepInstr, Jvm.stepInvokeStaticGeneric, mkCalcHooks, normalizeCalcClass]
  rfl

theorem runFast_makeConcat_gt {d f pc fuel : Nat} {prog rest : List JvmInstr}
    {s : String} {stack : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap CalcExt} {hp : CalcHeap} :
    Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) (fuel + 1) prog pc
        (.invokedynamic "makeConcatWithConstants" "> \x01" "(Ljava/lang/String;)Ljava/lang/String;" :: rest)
        ⟨pc, .str s :: stack, locs, jh, hp⟩ =
      Jvm.runJvmResFast (mkCalcHooks calcProgLookup (d + 1) f) fuel prog (pc + 1) rest
        ⟨pc + 1, .str ("> " ++ s) :: stack, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr _ rfl (by simp) ?_ rfl
  have hmc : Jvm.evalMakeConcatWithConstants "> \x01" "(Ljava/lang/String;)Ljava/lang/String;" (.str s :: stack) =
      some ("> " ++ s, stack) := by
    dsimp [Jvm.evalMakeConcatWithConstants]
    have hpt : Jvm.parseMethodParamTags "(Ljava/lang/String;)Ljava/lang/String;" = ['L'] := rfl
    rw [hpt]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    have hnot : ¬(stack.length + 1 < 1) := by omega
    rw [ite_eq_right (fun h => hnot h)]
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.zip_cons_cons, List.zip_nil_right]
    have heq : ("> " ++ s) = String.singleton '>' ++ (String.singleton ' ' ++ (s ++ "")) := by
      have hs1 : String.singleton '>' = ">" := rfl
      have hs2 : String.singleton ' ' = " " := rfl
      have hgt : "> " = ">" ++ " " := rfl
      rw [hs1, hs2, hgt, String.append_assoc, String.append_empty]
    change (match (some (String.singleton '>' ++ (String.singleton ' ' ++ (s ++ ""))), stack).1 with
      | some s' => some (s', stack) | none => none) = _
    dsimp only
    rw [← heq]
  dsimp [Jvm.stepInstr]
  rw [hmc]

end MosaicCalculator.KotlinJvmVerification

/*
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
 */

package com.alexvanyo.composelife.ui.util

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `EasingPiecewise.kt` by lifting the actual compiled
 * `EasingPiecewiseKt.class` JVM bytecode from the test runtime classpath into Lean 4 and proving theorems about that
 * real bytecode with `lake env lean`.
 */
class EasingPiecewiseVerificationTests {
    @Test
    fun floorBinarySearch_bytecode_finds_floor_index_and_traps_on_empty_keys() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_floorBinarySearch_finds_floor_index",
            leanBody = """
                |theorem real_floorBinarySearch_finds_floor_index
                |    (resolveProg : String → Option (List JvmInstr)) (d sf : Nat)
                |    (k0 : Float32) (rest : List Float32) (hlen : rest.length + 1 < 2 ^ 30) (value t : Float32)
                |    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) :
                |    (∃ idx : Int,
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) (21 * (rest.length + 1) + 20)
                |            UiCommon.RealJvmBytecode.EasingPiecewiseKt_floorBinarySearch_prog
                |            (initUiJvmState [(0, .ext (.floatList (k0 :: rest))), (1, .ext (.boxedFloat value))]
                |              hp jh) =
                |          some (.i32 (Int32.ofInt idx).toUInt32, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (idx = -1 ↔ floatCompare value k0 < 0) ∧
                |      (¬ floatCompare value k0 < 0 →
                |        ∃ i : Nat, idx = (i : Int) ∧ i < rest.length + 1 ∧
                |          floatCompare (k0 :: rest)[i]! value ≤ 0 ∧
                |          (i + 1 = rest.length + 1 ∨
                |            (i + 1 < rest.length + 1 ∧ floatCompare value (k0 :: rest)[i + 1]! < 0)))) ∧
                |    Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) 10 UiCommon.RealJvmBytecode.EasingPiecewiseKt_floorBinarySearch_prog
                |      (initUiJvmState [(0, .ext (.floatList [])), (1, .ext (.boxedFloat t))] hp jh) = none := by
                |  have hF : UiCommon.RealJvmBytecode.EasingPiecewiseKt_floorBinarySearch_prog =
                |      UiCommon.KotlinJvmBytecode.EasingPiecewiseKt_floorBinarySearch_prog := rfl
                |  rw [hF]
                |  have hne : 0 < (k0 :: rest).length := Nat.succ_pos _
                |  exact ⟨⟨_, floorBinarySearch_equiv resolveProg d sf _ (k0 :: rest) value (List.cons_ne_nil _ _) hlen
                |      (Nat.le_refl _) hp jh,
                |    floorBinarySearch_neg_one_iff (k0 :: rest) value hne,
                |    fun hge => floorBinarySearch_nonneg_bounds (k0 :: rest) value hne hge⟩,
                |    floorBinarySearch_empty_trap resolveProg d sf 10 (Nat.le_refl _) t hp jh⟩
            """.trimMargin(),
        )
    }

    @Test
    fun easing_lambda_bytecode_evaluates_piecewise_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_easing_lambda_evaluates_piecewise_model",
            leanBody = """
                |theorem real_easing_lambda_evaluates_piecewise_model
                |    (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
                |    (hext : ExtendsUiProgs resolveProg) (keys : List Float32) (es : List UiEasing) (t : Float32)
                |    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt) (hlen : keys.length < 2 ^ 30)
                |    (hes : ∀ e ∈ es, ∃ eid, e = .const eid ∧ eid < hp.easings.size)
                |    (hsf : 21 * keys.length + 20 ≤ sf) (hf : 60 ≤ fuel) :
                |    (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) fuel
                |        UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog
                |        (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.easingList es)), (2, .f32 t)]
                |          hp jh)).map
                |      (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
                |      (evalPiecewiseEasing (constEasingTransform hp) keys es t).map (fun v => (.f32 v, jh, hp)) := by
                |  have hL : UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog =
                |      UiCommon.KotlinJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog := rfl
                |  rw [hL]
                |  exact Easing_lambda_3_equiv resolveProg d sf fuel hext keys es t hp jh hlen hes hsf hf
            """.trimMargin(),
        )
    }

    @Test
    fun easing_factory_bytecode_validates_keyframes_and_allocates_closure() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_easing_factory_validates_keyframes",
            leanBody = """
                |theorem real_easing_factory_validates_keyframes
                |    (resolveProg : String → Option (List JvmInstr)) (d sf fuel : Nat)
                |    (e0 : UiEasing) (ps : List (Float32 × UiEasing)) (arrAddr : Nat) (cls : String)
                |    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt)
                |    (hget : jh.get? arrAddr = some (.objArray cls (ps.map encodeEasingPair).toArray))
                |    (hlen : ps.length < 2 ^ 30) (hf : 90 ≤ fuel) :
                |    (Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_prog
                |        (initUiJvmState [(0, .ext (.easing e0)), (1, .heapRef arrAddr)] hp jh)).map
                |      (fun r => (r.1, r.2.jvmHeap, r.2.heap)) =
                |      (validateEasingKeyframes e0 ps).map (fun ke =>
                |        (.ext (.easing (.piecewise hp.closures.size)), jh,
                |          { hp with
                |            maps := hp.maps.push (buildKeyframeMap e0 ps)
                |            closures := hp.closures.push
                |              ("EasingPiecewiseKt.Easing${'$'}lambda${'$'}3",
                |                [.ext (.floatList ke.1), .ext (.easingList ke.2)]) })) ∧
                |    (isSortedByKeyframe ps = false →
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg d sf) fuel UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_prog
                |        (initUiJvmState [(0, .ext (.easing e0)), (1, .heapRef arrAddr)] hp jh) = none) := by
                |  have hE : UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_prog = UiCommon.KotlinJvmBytecode.EasingPiecewiseKt_Easing_prog := rfl
                |  rw [hE]
                |  have hEq := Easing_equiv resolveProg d sf fuel e0 ps arrAddr cls hp jh hget hlen hf
                |  refine ⟨hEq, fun hunsorted => ?_⟩
                |  have hnone : validateEasingKeyframes e0 ps = none := by
                |    simp [validateEasingKeyframes, hunsorted]
                |  rw [hnone, Option.map_none] at hEq
                |  exact Option.map_eq_none_iff.mp hEq
            """.trimMargin(),
        )
    }

    @Test
    fun easing_factory_then_lambda_bytecode_evaluates_validated_keyframes() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_easing_factory_then_lambda",
            leanBody = """
                |theorem real_easing_factory_then_lambda
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsUiProgs resolveProg)
                |    (d sf : Nat) (eid0 : Nat) (ps : List (Float32 × UiEasing)) (arrAddr : Nat) (cls : String)
                |    (hp : UiHeap) (jh : Jvm.JvmHeap UiExt)
                |    (hget : jh.get? arrAddr = some (.objArray cls (ps.map encodeEasingPair).toArray))
                |    (hlen : ps.length + 1 < 2 ^ 30) (hsf : 21 * ps.length + 41 ≤ sf)
                |    (keys : List Float32) (es : List UiEasing)
                |    (hval : validateEasingKeyframes (.const eid0) ps = some (keys, es))
                |    (hes : ∀ e ∈ es, ∃ eid, e = .const eid ∧ eid < hp.easings.size) (t : Float32) :
                |    ∃ res st,
                |      Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) 90 UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_prog
                |          (initUiJvmState [(0, .ext (.easing (.const eid0))), (1, .heapRef arrAddr)] hp jh) =
                |        some (res, st) ∧
                |      st.heap.closures.back? =
                |        some ("EasingPiecewiseKt.Easing${'$'}lambda${'$'}3",
                |          [.ext (.floatList keys), .ext (.easingList es)]) ∧
                |      (Jvm.runJvmRes (mkUiCommonHooks resolveProg (d + 1) sf) 60
                |          UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog
                |          (initUiJvmState [(0, .ext (.floatList keys)), (1, .ext (.easingList es)), (2, .f32 t)]
                |            st.heap st.jvmHeap)).map Prod.fst =
                |        (evalPiecewiseEasing (constEasingTransform hp) keys es t).map .f32 := by
                |  have hE : UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_prog = UiCommon.KotlinJvmBytecode.EasingPiecewiseKt_Easing_prog := rfl
                |  have hL : UiCommon.RealJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog =
                |      UiCommon.KotlinJvmBytecode.EasingPiecewiseKt_Easing_lambda_3_prog := rfl
                |  rw [hE, hL]
                |  obtain ⟨hkeys, -, -, -, -, -⟩ := validateEasingKeyframes_strict_increasing _ ps keys es hval
                |  have hklen : keys.length = ps.length + 1 := by rw [hkeys]; simp
                |  have hfac := Easing_equiv resolveProg (d + 1) sf 90 (.const eid0) ps arrAddr cls hp jh hget
                |    (by omega) (Nat.le_refl _)
                |  rw [hval] at hfac
                |  obtain ⟨⟨res, st⟩, hrun, hproj⟩ := Option.map_eq_some_iff.mp hfac
                |  simp only [Prod.mk.injEq] at hproj
                |  obtain ⟨-, -, hheap⟩ := hproj
                |  have hlam := Easing_lambda_3_equiv resolveProg d sf 60 hext keys es t st.heap st.jvmHeap
                |    (by omega) (by rw [hheap]; exact hes) (by omega) (Nat.le_refl _)
                |  have hT : constEasingTransform st.heap = constEasingTransform hp := by
                |    rw [hheap]; rfl
                |  refine ⟨res, st, hrun, by rw [hheap]; exact Array.back?_push, ?_⟩
                |  have hfst := congrArg (Option.map Prod.fst) hlam
                |  simp only [Option.map_map] at hfst
                |  rw [hT] at hfst
                |  exact hfst
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "ui-common",
            classResourcePath = "com/alexvanyo/composelife/ui/util/EasingPiecewiseKt.class",
            realBytecodeNamespace = "UiCommon.RealJvmBytecode",
            instrType = "UiCommon.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "EasingPiecewiseKt_Easing_prog",
                "EasingPiecewiseKt_floorBinarySearch_prog",
                "EasingPiecewiseKt_Easing_lambda_3_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.EasingPiecewiseModel",
                "theorems.EasingPiecewiseModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.EasingPiecewise",
                "proofs.KotlinJvmEquiv.EasingLambda",
                "proofs.KotlinJvmEquiv.EasingFactory",
            ),
            defaultOpens = listOf(
                "UiCommon",
                "UiCommon.JvmVerification",
                "UiCommon.Model",
                "UiCommon.KotlinJvmVerification",
            ),
        )
    }
}

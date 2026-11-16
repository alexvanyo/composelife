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

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `BitComputation.kt` by lifting
 * the actual compiled `BitComputationKt.class` JVM bytecode from the test runtime classpath into
 * Lean 4 and proving theorems about that real bytecode with `lake env lean`.
 */
class BitComputationVerificationTests {
    @Test
    fun computeQuadInfo_bytecode_implements_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_computeQuadInfo_implements_model",
            leanBody = """
                |theorem real_computeQuadInfo_implements_model
                |    (q : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    ∃ r : UInt32,
                |      runJvm 150 Algorithm.RealJvmBytecode.BitComputationKt_computeQuadInfo_prog
                |        (Jvm.initJvmState [(0, .i32 q)] (.i32 0) hp jh) = some (.i32 r) ∧
                |      r = computeQuadInfoModel q ∧
                |      (r &&& (0xF : UInt32) = Algorithm.extractCenterUInt q) ∧
                |      (((r >>> 4) &&& (0x5 : UInt32)) =
                |        (((q >>> 7) &&& (1 : UInt32)) ||| (((q >>> 13) &&& (1 : UInt32)) <<< 2))) ∧
                |      (((r >>> 8) &&& (0xA : UInt32)) =
                |        ((((q >>> 2) &&& (1 : UInt32)) <<< 1) ||| (((q >>> 8) &&& (1 : UInt32)) <<< 3))) ∧
                |      (((r >>> 12) &&& (0x3 : UInt32)) =
                |        (((q >>> 11) &&& (1 : UInt32)) ||| (((q >>> 14) &&& (1 : UInt32)) <<< 1))) ∧
                |      (((r >>> 16) &&& (0xC : UInt32)) =
                |        ((((q >>> 1) &&& (1 : UInt32)) <<< 2) ||| (((q >>> 4) &&& (1 : UInt32)) <<< 3))) ∧
                |      ((r >>> 20) &&& (0xF : UInt32) =
                |        (((q >>> 15) &&& (1 : UInt32)) ||| (((q >>> 10) &&& (1 : UInt32)) <<< 1) |||
                |          (((q >>> 5) &&& (1 : UInt32)) <<< 2) ||| ((q &&& (1 : UInt32)) <<< 3))) ∧
                |      r < 0x1000000 := by
                |  have hprog : Algorithm.RealJvmBytecode.BitComputationKt_computeQuadInfo_prog =
                |      Algorithm.KotlinJvmBytecode.BitComputationKt_computeQuadInfo_prog := rfl
                |  rw [hprog]
                |  rcases computeQuadInfoModel_bitSpec q with ⟨h1, h2, h3, h4, h5, h6, h7⟩
                |  exact ⟨computeQuadInfoModel q, computeQuadInfo_equiv q jh hp, rfl, h1, h2, h3, h4, h5, h6, h7⟩
            """.trimMargin(),
        )
    }

    @Test
    fun clinit_bytecode_initializes_quad_info_lut() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_clinit_initializes_quad_info_lut",
            leanBody = """
                |theorem real_clinit_initializes_quad_info_lut :
                |    ∃ st',
                |      runJvmRes 800000 Algorithm.RealJvmBytecode.BitComputationKt_clinit_prog
                |        ⟨0, [], fun _ => .i32 0, {}, ⟨[], [], []⟩⟩ = some (.unit, st') ∧
                |      HasQuadInfoLut st'.jvmHeap := by
                |  have hprog : Algorithm.RealJvmBytecode.BitComputationKt_clinit_prog =
                |      Algorithm.KotlinJvmBytecode.BitComputationKt_clinit_prog := rfl
                |  rw [hprog]
                |  exact clinit_BitComputationKt_equiv
            """.trimMargin(),
        )
    }

    @Test
    fun computeNextGen4x4_bytecode_matches_conway_bitwise() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_computeNextGen4x4_matches_conway_bitwise",
            leanBody = """
                |theorem real_computeNextGen4x4_matches_conway_bitwise
                |    (w : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hlut : HasNextGen4x4Lut jh) :
                |    runJvm 30 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGen4x4_prog
                |      (Jvm.initJvmState [(0, .i32 w)] (.i32 0) hp jh) =
                |      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt (w &&& 0xFFFF) &&& 0xF)) := by
                |  have hprog : Algorithm.RealJvmBytecode.BitComputationKt_computeNextGen4x4_prog =
                |      Algorithm.KotlinJvmBytecode.BitComputationKt_computeNextGen4x4_prog := rfl
                |  rw [hprog]
                |  exact computeNextGen4x4_equiv w jh hp hlut
            """.trimMargin(),
        )
    }

    @Test
    fun long_computeNextGenerationPureKotlin_bytecode_implements_conways_game_of_life() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_long_computeNextGenerationPureKotlin_implements_life",
            leanBody = """
                |theorem real_long_computeNextGenerationPureKotlin_implements_life
                |    (w c : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
                |    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh)
                |    (x y : Int) (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6)
                |    (hc : c &&& ~~~outerCornerMask = 0) :
                |    (∃ r : UInt32,
                |      runJvm 250 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog
                |        (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) = some (.i32 r) ∧
                |      r.toBitVec.getLsbD (Algorithm.mortonIndex4 (x - 2).toNat (y - 2).toNat) =
                |        Algorithm.nextGenAt (Algorithm.leafAt w) x y ∧
                |      r.toNat < 65536) ∧
                |    runJvm 250 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog
                |      (Jvm.initJvmState [(0, .i64 0)] (.i32 0) hp jh) = some (.i32 0) ∧
                |    runJvm 250 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog
                |      (Jvm.initJvmState [(0, .i64 (w ^^^ c))] (.i32 0) hp jh) =
                |    runJvm 250 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog
                |      (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) := by
                |  have hprog : Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog =
                |      Algorithm.KotlinJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_prog := rfl
                |  rw [hprog]
                |  refine ⟨⟨computeNextGenerationPureKotlinModel w, ?_, ?_, ?_⟩, ?_, ?_⟩
                |  · exact computeNextGenerationPureKotlin_equiv w jh hp hqi hng
                |  · exact computeNextGenerationPureKotlinModel_correct w x y hx hy
                |  · exact computeNextGenerationPureKotlinModel_lt_65536 w
                |  · rw [computeNextGenerationPureKotlin_equiv 0 jh hp hqi hng, computeNextGenerationPureKotlinModel_zero]
                |  · rw [computeNextGenerationPureKotlin_equiv (w ^^^ c) jh hp hqi hng,
                |      computeNextGenerationPureKotlin_equiv w jh hp hqi hng,
                |      computeNextGenerationPureKotlinModel_corner_indep w c hc]
            """.trimMargin(),
        )
    }

    @Test
    fun ulong_computeNextGenerationPureKotlin_bridge_matches_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_ulong_computeNextGenerationPureKotlin_matches_life_fast",
            leanBody = """
                |theorem real_ulong_computeNextGenerationPureKotlin_matches_life_fast
                |    (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
                |    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
                |    runJvm 10 Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_1_prog
                |      (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |      some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w)) := by
                |  have hprog : Algorithm.RealJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_1_prog =
                |      Algorithm.KotlinJvmBytecode.BitComputationKt_computeNextGenerationPureKotlin_1_prog := rfl
                |  rw [hprog, computeNextGenerationPureKotlin_1_equiv w jh hp hqi hng,
                |    computeNextGenerationPureKotlinModel_eq_fast w]
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/algorithm/BitComputationKt.class",
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Algorithm.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "BitComputationKt_computeNextGen4x4_prog",
                "BitComputationKt_computeQuadInfo_prog",
                "BitComputationKt_computeNextGenerationPureKotlin_prog",
                "BitComputationKt_computeNextGenerationPureKotlin_1_prog",
                "BitComputationKt_clinit_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.BitComputationModel",
                "theorems.BitComputationModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.BitComputation",
            ),
            defaultOpens = listOf(
                "Algorithm.JvmVerification",
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

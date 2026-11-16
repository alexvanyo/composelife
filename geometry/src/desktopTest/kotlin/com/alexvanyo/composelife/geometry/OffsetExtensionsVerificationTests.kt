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

package com.alexvanyo.composelife.geometry

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `OffsetExtensions.kt` against the
 * live `OffsetExtensionsKt.class` bytecode lifted into Lean 4.
 */
class OffsetExtensionsVerificationTests {
    @Test
    fun toRingIndex_bytecode_origin_and_shell_bounds() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_toRingIndex_origin_and_shell_bounds",
            leanBody = """
                |theorem real_toRingIndex_origin_and_shell_bounds
                |    (x y : Int32) (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169) :
                |    runJvm 15 Geometry.RealJvmBytecode.OffsetExtensionsKt_toRingIndex_prog
                |      (initJvmState [(0, .i64 0)]) = some (.i32 0) ∧
                |    (∃ idx : Int32,
                |      runJvm 120 Geometry.RealJvmBytecode.OffsetExtensionsKt_toRingIndex_prog
                |        (initJvmState [(0, .i64 (packOffset x y))]) =
                |        some (.i32 idx.toUInt32) ∧
                |      idx.toInt = toRingIndexMath x.toInt y.toInt ∧
                |      (x = 0 ∧ y = 0 → idx = 0) ∧
                |      (let r : Int := max x.toInt.natAbs y.toInt.natAbs
                |       1 ≤ r →
                |       (2 * (r - 1) + 1) * (2 * (r - 1) + 1) ≤ idx.toInt ∧
                |       idx.toInt < (2 * r + 1) * (2 * r + 1))) := by
                |  have hprog : Geometry.RealJvmBytecode.OffsetExtensionsKt_toRingIndex_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_toRingIndex_prog := rfl
                |  rw [hprog]
                |  refine ⟨toRingIndex_zero_equiv, ?_⟩
                |  rcases toRingIndex_equiv_of_bounded x y hx hy with
                |    ⟨idx, hrun, _, hmath, hz, hsh⟩
                |  exact ⟨idx, hrun, hmath, hz, hsh⟩
            """.trimMargin(),
        )
    }

    @Test
    fun toIntOffset_toPair_bytecode_roundtrip() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_toIntOffset_toPair_roundtrip",
            leanBody = """
                |theorem real_toIntOffset_toPair_roundtrip (x y : Int32) :
                |    ∃ packed : UInt64,
                |      runJvm 35 Geometry.RealJvmBytecode.OffsetExtensionsKt_toIntOffset_prog
                |        (initJvmState [(0, .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32))]) =
                |        some (.i64 packed) ∧
                |      runJvm 20 Geometry.RealJvmBytecode.OffsetExtensionsKt_toPair_prog
                |        (initJvmState [(0, .i64 packed)]) =
                |        some (.pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)) := by
                |  have hprog1 : Geometry.RealJvmBytecode.OffsetExtensionsKt_toIntOffset_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_toIntOffset_prog := rfl
                |  have hprog2 : Geometry.RealJvmBytecode.OffsetExtensionsKt_toPair_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_toPair_prog := rfl
                |  rw [hprog1, hprog2]
                |  refine ⟨packOffset x y, toIntOffset_equiv x y, ?_⟩
                |  rw [toPair_equiv (packOffset x y), offsetX_pack, offsetY_pack]
            """.trimMargin(),
        )
    }

    @Test
    fun euclideanDistance_toPx_and_toRingOffset_bytecode_semantics() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_offset_f32_and_zero_ring_offset",
            leanBody = """
                |theorem real_offset_f32_and_zero_ring_offset
                |    (calcDistance : UInt64 → Float32) (densityToPx : Float32 → Float32)
                |    (o dp : UInt64) :
                |    Jvm.runJvm (mkGeomHooks calcDistance densityToPx) 45
                |      Geometry.RealJvmBytecode.OffsetExtensionsKt_euclideanDistance_prog
                |      (initJvmState [(0, .i64 o)]) =
                |      some (.f32 (calcDistance (
                |        ((Jvm.i32ToFloat32 (offsetX o).toUInt32).toBits.toUInt64 <<< 32) |||
                |        (Jvm.i32ToFloat32 (offsetY o).toUInt32).toBits.toUInt64))) ∧
                |    Jvm.runJvm (mkGeomHooks calcDistance densityToPx) 45
                |      Geometry.RealJvmBytecode.OffsetExtensionsKt_toPx_prog
                |      (initJvmState
                |        [(0, .allocRef "androidx/compose/ui/unit/Density"), (1, .i64 dp)]) =
                |      some (.i64 (
                |        ((densityToPx (Float32.ofBits (dp >>> 32).toUInt32)).toBits.toUInt64 <<< 32) |||
                |        (densityToPx (Float32.ofBits dp.toUInt32)).toBits.toUInt64)) ∧
                |    runJvm 15 Geometry.RealJvmBytecode.OffsetExtensionsKt_toRingOffset_prog
                |      (initJvmState [(0, .i32 0)]) = some (.i64 0) := by
                |  have hprogE : Geometry.RealJvmBytecode.OffsetExtensionsKt_euclideanDistance_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_euclideanDistance_prog := rfl
                |  have hprogP : Geometry.RealJvmBytecode.OffsetExtensionsKt_toPx_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_toPx_prog := rfl
                |  have hprogO : Geometry.RealJvmBytecode.OffsetExtensionsKt_toRingOffset_prog =
                |      Geometry.KotlinJvmBytecode.OffsetExtensionsKt_toRingOffset_prog := rfl
                |  rw [hprogE, hprogP, hprogO]
                |  exact ⟨euclideanDistance_equiv calcDistance densityToPx o,
                |    toPx_equiv calcDistance densityToPx dp,
                |    toRingOffset_zero_equiv⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "geometry",
            classResourcePath = "com/alexvanyo/composelife/geometry/OffsetExtensionsKt.class",
            realBytecodeNamespace = "Geometry.RealJvmBytecode",
            instrType = "Geometry.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "OffsetExtensionsKt_euclideanDistance_prog",
                "OffsetExtensionsKt_toPx_prog",
                "OffsetExtensionsKt_toRingIndex_prog",
                "OffsetExtensionsKt_toRingOffset_prog",
                "OffsetExtensionsKt_toIntOffset_prog",
                "OffsetExtensionsKt_toPair_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.SpiralRingModel",
                "proofs.SpiralRingModelProofs",
                "theorems.SpiralRingModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.OffsetExtensions",
            ),
            defaultOpens = listOf(
                "Geometry.JvmVerification",
                "Geometry.KotlinModel",
                "Geometry.KotlinJvmVerification",
            ),
        )
    }
}

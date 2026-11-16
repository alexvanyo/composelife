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
 * Standard `@Test` suite verifying hand-written Kotlin code in `GeometryExtensions.kt` by lifting
 * the actual compiled `GeometryExtensionsKt.class` JVM bytecode from the test runtime classpath into
 * Lean 4 and proving theorems about that real bytecode with `lake env lean`.
 */
class GeometryExtensionsVerificationTests {
    @Test
    fun chebyshevDistance_bytecode_metric_and_symmetry() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_chebyshevDistance_metric_and_symmetry",
            leanBody = """
                |theorem real_chebyshevDistance_metric_and_symmetry
                |    (p : UInt64) (x y : Int32)
                |    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue) :
                |    ∃ d : UInt32,
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 p)]) = some (.i32 d) ∧
                |      d.toInt32.toInt = max (offsetX p).toInt.natAbs (offsetY p).toInt.natAbs ∧
                |      d.toBitVec.slt 0#32 = false ∧
                |      (d = 0 ↔ p = 0) ∧
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 (packOffset (-x) (-y)))]) =
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 (packOffset x y))]) ∧
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 (packOffset x y))]) =
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 (packOffset y x))]) := by
                |  have hprog : Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog := rfl
                |  rw [hprog]
                |  rcases chebyshevDistanceModel_eq_natMax p hx hy with ⟨hmax, hnonneg⟩
                |  refine ⟨chebyshevDistanceModel p, chebyshevDistance_equiv p, hmax, hnonneg,
                |    chebyshevDistanceModel_eq_zero_iff p hx hy, ?_, ?_⟩
                |  · simp only [chebyshevDistance_equiv, chebyshevDistanceModel_neg]
                |  · simp only [chebyshevDistance_equiv, chebyshevDistanceModel_swap]
            """.trimMargin(),
        )
    }

    @Test
    fun manhattanDistance_bytecode_triangle_and_norm_equivalence() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_manhattanDistance_triangle_and_norm_equiv",
            leanBody = """
                |theorem real_manhattanDistance_triangle_and_norm_equiv
                |    (p a b : UInt64) (x y : Int32)
                |    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue)
                |    (hsum : (offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs < 2 ^ 31)
                |    (hax : -((2 ^ 28 : Int)) ≤ (offsetX a).toInt ∧ (offsetX a).toInt ≤ 2 ^ 28)
                |    (hay : -((2 ^ 28 : Int)) ≤ (offsetY a).toInt ∧ (offsetY a).toInt ≤ 2 ^ 28)
                |    (hbx : -((2 ^ 28 : Int)) ≤ (offsetX b).toInt ∧ (offsetX b).toInt ≤ 2 ^ 28)
                |    (hby : -((2 ^ 28 : Int)) ≤ (offsetY b).toInt ∧ (offsetY b).toInt ≤ 2 ^ 28) :
                |    (∃ dInf d1 : UInt32,
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |        (initJvmState [(0, .i64 p)]) = some (.i32 dInf) ∧
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |        (initJvmState [(0, .i64 p)]) = some (.i32 d1) ∧
                |      dInf.toInt32.toInt ≤ d1.toInt32.toInt ∧
                |      d1.toInt32.toInt ≤ 2 * dInf.toInt32.toInt) ∧
                |    (∃ dab da db : UInt32,
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |        (initJvmState [(0, .i64 (addPackedOffset a b))]) = some (.i32 dab) ∧
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |        (initJvmState [(0, .i64 a)]) = some (.i32 da) ∧
                |      runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |        (initJvmState [(0, .i64 b)]) = some (.i32 db) ∧
                |      dab.toInt32.toInt ≤ da.toInt32.toInt + db.toInt32.toInt) ∧
                |    runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |      (initJvmState [(0, .i64 (packOffset (-x) (-y)))]) =
                |    runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |      (initJvmState [(0, .i64 (packOffset y x))]) := by
                |  have hprogC : Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog := rfl
                |  have hprogM : Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog := rfl
                |  rw [hprogC, hprogM]
                |  refine ⟨chebyshev_manhattan_norm_equiv_bytecode p hx hy hsum, ?_, ?_⟩
                |  · exact ⟨manhattanDistanceModel (addPackedOffset a b),
                |      manhattanDistanceModel a, manhattanDistanceModel b,
                |      manhattanDistance_equiv _, manhattanDistance_equiv _, manhattanDistance_equiv _,
                |      manhattanDistanceModel_triangle a b hax hay hbx hby⟩
                |  · simp only [manhattanDistance_equiv, manhattanDistanceModel_neg, manhattanDistanceModel_swap]
            """.trimMargin(),
        )
    }

    @Test
    fun clinit_and_getMooreNeighbors_bytecode_unit_sphere() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_getMooreNeighbors_unit_sphere",
            leanBody = """
                |theorem real_getMooreNeighbors_unit_sphere (o : UInt64) :
                |    ∃ st0 setAddr st1 neighbors,
                |      runJvmRes 100 Geometry.RealJvmBytecode.GeometryExtensionsKt_clinit_prog
                |        (initJvmState [] {}) = some (.unit, st0) ∧
                |      runJvmRes 214 Geometry.RealJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog
                |        (initJvmState [(0, .i64 o)] st0.jvmHeap) =
                |        some (.heapRef setAddr, st1) ∧
                |      extractPackedSet? st1.jvmHeap (.heapRef setAddr) = some neighbors ∧
                |      neighbors.length = 8 ∧
                |      neighbors.Nodup ∧
                |      ∀ n ∈ neighbors,
                |        runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog
                |          (initJvmState [(0, .i64 (subPackedOffset n o))]) = some (.i32 1) := by
                |  have hprogCl : Geometry.RealJvmBytecode.GeometryExtensionsKt_clinit_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_clinit_prog := rfl
                |  have hprogM : Geometry.RealJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog := rfl
                |  have hprogC : Geometry.RealJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_chebyshevDistance_prog := rfl
                |  rw [hprogCl, hprogM, hprogC]
                |  exact getMooreNeighbors_bytecode_unit_sphere o
            """.trimMargin(),
        )
    }

    @Test
    fun clinit_and_getVonNeumannNeighbors_bytecode_unit_sphere_subset() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_getVonNeumannNeighbors_unit_sphere_subset",
            leanBody = """
                |theorem real_getVonNeumannNeighbors_unit_sphere_subset (o : UInt64) :
                |    ∃ st0 vSet mSet stV stM vNeighbors mNeighbors,
                |      runJvmRes 100 Geometry.RealJvmBytecode.GeometryExtensionsKt_clinit_prog
                |        (initJvmState [] {}) = some (.unit, st0) ∧
                |      runJvmRes 122 Geometry.RealJvmBytecode.GeometryExtensionsKt_getVonNeumannNeighbors_prog
                |        (initJvmState [(0, .i64 o)] st0.jvmHeap) =
                |        some (.heapRef vSet, stV) ∧
                |      runJvmRes 214 Geometry.RealJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog
                |        (initJvmState [(0, .i64 o)] st0.jvmHeap) =
                |        some (.heapRef mSet, stM) ∧
                |      extractPackedSet? stV.jvmHeap (.heapRef vSet) = some vNeighbors ∧
                |      extractPackedSet? stM.jvmHeap (.heapRef mSet) = some mNeighbors ∧
                |      vNeighbors.length = 4 ∧
                |      vNeighbors.Nodup ∧
                |      (∀ n ∈ vNeighbors,
                |        runJvm 15 Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog
                |          (initJvmState [(0, .i64 (subPackedOffset n o))]) = some (.i32 1)) ∧
                |      (∀ n ∈ vNeighbors, n ∈ mNeighbors) := by
                |  have hprogCl : Geometry.RealJvmBytecode.GeometryExtensionsKt_clinit_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_clinit_prog := rfl
                |  have hprogV : Geometry.RealJvmBytecode.GeometryExtensionsKt_getVonNeumannNeighbors_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_getVonNeumannNeighbors_prog := rfl
                |  have hprogM : Geometry.RealJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_getMooreNeighbors_prog := rfl
                |  have hprogMan : Geometry.RealJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog =
                |      Geometry.KotlinJvmBytecode.GeometryExtensionsKt_manhattanDistance_prog := rfl
                |  rw [hprogCl, hprogV, hprogM, hprogMan]
                |  exact getVonNeumannNeighbors_bytecode_unit_sphere_subset o
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "geometry",
            classResourcePath = "com/alexvanyo/composelife/geometry/GeometryExtensionsKt.class",
            realBytecodeNamespace = "Geometry.RealJvmBytecode",
            instrType = "Geometry.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "GeometryExtensionsKt_chebyshevDistance_prog",
                "GeometryExtensionsKt_manhattanDistance_prog",
                "GeometryExtensionsKt_getMooreNeighbors_prog",
                "GeometryExtensionsKt_getVonNeumannNeighbors_prog",
                "GeometryExtensionsKt_clinit_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.GeometryExtensionsModel",
                "proofs.GeometryExtensionsModelProofs",
                "theorems.GeometryExtensionsModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.GeometryExtensions",
            ),
            defaultOpens = listOf(
                "Geometry.JvmVerification",
                "Geometry.KotlinModel",
                "Geometry.KotlinJvmVerification",
            ),
        )
    }
}

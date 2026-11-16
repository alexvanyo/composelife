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
 * Standard `@Test` suite verifying hand-written Kotlin code in `HashLifeComputation.kt` by lifting the actual compiled
 * `HashLifeComputationKt.class` JVM bytecode (and its two `ULong::computeNextGenerationPureKotlin` function-reference
 * classes) from the test runtime classpath into Lean 4 and proving theorems about that real bytecode with
 * `lake env lean`.
 */
class HashLifeComputationVerificationTests {
    @Test
    fun packLeafNode_and_quadrant_getters_bytecode_round_trip() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_packLeafNode_quadrants_round_trip",
            leanBody = """
                |theorem real_packLeafNode_quadrants_round_trip
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel : Nat) (nw ne sw se : UInt32)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    ∃ w : UInt64,
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 28
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_packLeafNode_prog
                |          (Jvm.initJvmState [(0, .i32 nw), (1, .i32 ne), (2, .i32 sw), (3, .i32 se)] (.i32 0) hp jh) =
                |        some (.i64 w, endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 8
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_getNw_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |        some (.i32 (nw &&& 0xffff), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 11
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_getNe_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |        some (.i32 (ne &&& 0xffff), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 11
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_getSw_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |        some (.i32 (sw &&& 0xffff), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 8
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_getSe_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |        some (.i32 (se &&& 0xffff), endSt) ∧ endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have hP : Algorithm.RealJvmBytecode.HashLifeComputationKt_packLeafNode_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_packLeafNode_prog := rfl
                |  have hNw : Algorithm.RealJvmBytecode.HashLifeComputationKt_getNw_prog = Algorithm.KotlinJvmBytecode.HashLifeComputationKt_getNw_prog := rfl
                |  have hNe : Algorithm.RealJvmBytecode.HashLifeComputationKt_getNe_prog = Algorithm.KotlinJvmBytecode.HashLifeComputationKt_getNe_prog := rfl
                |  have hSw : Algorithm.RealJvmBytecode.HashLifeComputationKt_getSw_prog = Algorithm.KotlinJvmBytecode.HashLifeComputationKt_getSw_prog := rfl
                |  have hSe : Algorithm.RealJvmBytecode.HashLifeComputationKt_getSe_prog = Algorithm.KotlinJvmBytecode.HashLifeComputationKt_getSe_prog := rfl
                |  rw [hP, hNw, hNe, hSw, hSe]
                |  refine ⟨packLeafNodeModel nw ne sw se, packLeafNode_equiv resolveProg d subFuel 28 (Nat.le_refl _)
                |    nw ne sw se jh hp, ?_, ?_, ?_, ?_⟩
                |  · rw [← packLeafNode_leafNw nw ne sw se]
                |    exact getNw_equiv resolveProg d subFuel 8 (Nat.le_refl _) _ jh hp
                |  · rw [← packLeafNode_leafNe nw ne sw se]
                |    exact getNe_equiv resolveProg d subFuel 11 (Nat.le_refl _) _ jh hp
                |  · rw [← packLeafNode_leafSw nw ne sw se]
                |    exact getSw_equiv resolveProg d subFuel 11 (Nat.le_refl _) _ jh hp
                |  · rw [← packLeafNode_leafSe nw ne sw se]
                |    exact getSe_equiv resolveProg d subFuel 8 (Nat.le_refl _) _ jh hp
            """.trimMargin(),
        )
    }

    @Test
    fun centered_subnode_bytecode_extracts_the_centered_cells() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_centered_subnodes_extract_center",
            leanBody = """
                |theorem real_centered_subnodes_extract_center
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat) (hf : 68 ≤ fuel)
                |    (nw ne sw se : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    (∃ r endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredSubnodeLevel3_prog
                |        (Jvm.initJvmState [(0, .i64 nw)] (.i32 0) hp jh) = some (.i32 r, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp ∧
                |      ∀ lx ly : Int, 0 ≤ lx ∧ lx < 4 → 0 ≤ ly ∧ ly < 4 →
                |        Algorithm.grid4At r lx ly = Algorithm.leafAt nw (lx + 2) (ly + 2)) ∧
                |    (∃ r endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog
                |        (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne)] (.i32 0) hp jh) = some (.i32 r, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp ∧
                |      ∀ lx ly : Int, 0 ≤ lx ∧ lx < 4 → 0 ≤ ly ∧ ly < 4 →
                |        Algorithm.grid4At r lx ly = level4CellAt nw ne sw se (lx + 6) (ly + 2)) ∧
                |    (∃ r endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog
                |        (Jvm.initJvmState [(0, .i64 nw), (2, .i64 sw)] (.i32 0) hp jh) = some (.i32 r, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp ∧
                |      ∀ lx ly : Int, 0 ≤ lx ∧ lx < 4 → 0 ≤ ly ∧ ly < 4 →
                |        Algorithm.grid4At r lx ly = level4CellAt nw ne sw se (lx + 2) (ly + 6)) ∧
                |    (∃ r endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredSubSubnodeLevel4_prog
                |        (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)] (.i32 0) hp jh) =
                |          some (.i32 r, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp ∧
                |      ∀ lx ly : Int, 0 ≤ lx ∧ lx < 4 → 0 ≤ ly ∧ ly < 4 →
                |        Algorithm.grid4At r lx ly = level4CellAt nw ne sw se (lx + 6) (ly + 6)) := by
                |  have h1 : Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredSubnodeLevel3_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_centeredSubnodeLevel3_prog := rfl
                |  have h2 : Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog := rfl
                |  have h3 : Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog := rfl
                |  have h4 : Algorithm.RealJvmBytecode.HashLifeComputationKt_centeredSubSubnodeLevel4_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_centeredSubSubnodeLevel4_prog := rfl
                |  rw [h1, h2, h3, h4]
                |  obtain ⟨s1, r1, a1, b1⟩ := centeredSubnodeLevel3_equiv resolveProg d subFuel fuel hf nw jh hp
                |  obtain ⟨s2, r2, a2, b2⟩ :=
                |    centeredHorizontalSubnodeLevel3_equiv resolveProg d subFuel fuel hf nw ne jh hp
                |  obtain ⟨s3, r3, a3, b3⟩ :=
                |    centeredVerticalSubnodeLevel3_equiv resolveProg d subFuel fuel hf nw sw jh hp
                |  obtain ⟨s4, r4, a4, b4⟩ :=
                |    centeredSubSubnodeLevel4_equiv resolveProg d subFuel fuel hf nw ne sw se jh hp
                |  exact ⟨⟨_, s1, r1, a1, b1, fun lx ly hx hy => centeredSubnodeLevel3Model_correct nw lx ly hx hy⟩,
                |    ⟨_, s2, r2, a2, b2,
                |      fun lx ly hx hy => centeredHorizontalSubnodeLevel3Model_correct nw ne sw se lx ly hx hy⟩,
                |    ⟨_, s3, r3, a3, b3,
                |      fun lx ly hx hy => centeredVerticalSubnodeLevel3Model_correct nw ne sw se lx ly hx hy⟩,
                |    ⟨_, s4, r4, a4, b4,
                |      fun lx ly hx hy => centeredSubSubnodeLevel4Model_correct nw ne sw se lx ly hx hy⟩⟩
            """.trimMargin(),
        )
    }

    @Test
    fun computeNextGeneration_bytecode_runs_lean_leaf_kernel() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_computeNextGeneration_runs_lean_kernel",
            leanBody = """
                |theorem real_computeNextGeneration_runs_lean_kernel
                |    (resolveProg : String → Option (List JvmInstr))
                |    (hr : HashLifeComputation.ExtendsAlgKotlinProgs resolveProg) (d subFuel : Nat) (hd : 1 ≤ d)
                |    (hsf : 3 ≤ subFuel) (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 3
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_computeNextGeneration_prog
                |        (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 4
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_computeNextGeneration_1_prog
                |        (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
                |      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have h1 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeNextGeneration_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeNextGeneration_prog := rfl
                |  have h2 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeNextGeneration_1_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeNextGeneration_1_prog := rfl
                |  rw [h1, h2]
                |  exact ⟨computeNextGeneration_equiv resolveProg d subFuel 3 (Nat.le_refl _) w jh hp,
                |    computeNextGeneration_1_equiv resolveProg hr d subFuel 4 hd hsf (Nat.le_refl _) w jh hp⟩
            """.trimMargin(),
        )
    }

    @Test
    fun computeLevel4NextGeneration_bytecode_matches_lean_with_any_leaf_kernel() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_computeLevel4NextGeneration_matches_lean",
            leanBody = """
                |theorem real_computeLevel4NextGeneration_matches_lean
                |    (resolveProg : String → Option (List JvmInstr))
                |    (hr : HashLifeComputation.ExtendsAlgKotlinProgs resolveProg) (d subFuel : Nat) (hd : 2 ≤ d)
                |    (hsf : 95 ≤ subFuel) (h : UInt32) (nw ne sw se : UInt64) (g : UInt64 → UInt32)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 95
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_prog
                |        (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se),
                |          (8, .ext (.fnU64ToI32 g))] (.i32 0) hp jh) =
                |      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se g), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 17
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_prog
                |        (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, .ext (.fnU64ToI32 g))]
                |          (.i32 0) hp jh) =
                |      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se g), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have h1 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_prog := rfl
                |  have h2 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_prog := rfl
                |  rw [h1, h2, ← computeLevel4NextGenerationModel_eq_lean]
                |  exact ⟨computeLevel4NextGeneration_equiv resolveProg hr d subFuel 95 (by omega) (by omega)
                |      (Nat.le_refl _) nw ne sw se g jh hp,
                |    computeLevel4NextGeneration_1_equiv resolveProg hr d subFuel 17 hd hsf (Nat.le_refl _) h nw ne sw
                |      se g jh hp⟩
            """.trimMargin(),
        )
    }

    @Test
    fun computeLevel4NextGeneration_default_kernel_bytecode_implements_conways_game_of_life() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_computeLevel4NextGeneration_default_implements_life",
            leanBody = """
                |theorem real_computeLevel4NextGeneration_default_implements_life
                |    (resolveProg : String → Option (List JvmInstr))
                |    (hr : HashLifeComputation.ExtendsAlgKotlinProgs resolveProg) (d subFuel : Nat) (hd : 6 ≤ d)
                |    (hsf : 250 ≤ subFuel) (h : UInt32) (nw ne sw se : UInt64) (fn marker : JvmVal) (mask : UInt32)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh)
                |    (hinst1 : jh.getStatic? HashLifeComputation.lambdaClass1 "INSTANCE" = none ∨
                |      jh.getStatic? HashLifeComputation.lambdaClass1 "INSTANCE" =
                |        some (.allocRef HashLifeComputation.lambdaClass1))
                |    (hinst2 : jh.getStatic? HashLifeComputation.lambdaClass2 "INSTANCE" = none ∨
                |      jh.getStatic? HashLifeComputation.lambdaClass2 "INSTANCE" =
                |        some (.allocRef HashLifeComputation.lambdaClass2)) :
                |    ∃ out : UInt64,
                |      (mask &&& 16 ≠ 0 → ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 14
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog
                |          (Jvm.initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, fn),
                |            (9, .i32 mask), (10, marker)] (.i32 0) hp jh) = some (.i64 out, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (mask &&& 2 ≠ 0 → ∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 11
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_default_prog
                |          (Jvm.initJvmState [(0, .ext (.mc (.level4Node h nw ne sw se))), (1, fn), (2, .i32 mask),
                |            (3, marker)] (.i32 0) hp jh) = some (.i64 out, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      ∀ x y : Int, 0 ≤ x ∧ x < 8 → 0 ≤ y ∧ y < 8 →
                |        Algorithm.leafAt out x y = Algorithm.nextGenAt (level4CellAt nw ne sw se) (x + 4) (y + 4) := by
                |  have h1 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog := rfl
                |  have h2 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_default_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_default_prog := rfl
                |  rw [h1, h2]
                |  exact ⟨_,
                |    fun hm => computeLevel4NextGeneration_qFGr5tM_default_lambda_equiv resolveProg hr d subFuel 14
                |      (by omega) hsf (Nat.le_refl _) nw ne sw se fn mask hm marker jh hp hqi hng hinst1,
                |    fun hm => computeLevel4NextGeneration_default_lambda_equiv resolveProg hr d subFuel 11 hd hsf
                |      (Nat.le_refl _) h nw ne sw se fn mask hm marker jh hp hqi hng hinst2,
                |    fun x y hx hy => computeLevel4NextGenerationModel_correct nw ne sw se x y hx hy⟩
            """.trimMargin(),
        )
    }

    @Test
    fun function_reference_singletons_bytecode_run_pure_kotlin_kernel() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_function_references_run_pure_kotlin_kernel",
            leanBody = """
                |theorem real_function_references_run_pure_kotlin_kernel
                |    (resolveProg : String → Option (List JvmInstr))
                |    (hr : HashLifeComputation.ExtendsAlgKotlinProgs resolveProg)
                |    (hinit :
                |      resolveProg "HashLifeComputationKt${'$'}computeLevel4NextGeneration${'$'}1.<init>:()V" = none)
                |    (d subFuel : Nat) (hd : 3 ≤ d) (hsf : 250 ≤ subFuel) (w : UInt64)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh)
                |    (x y : Int) (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6) :
                |    (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 5
                |        Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog
                |        (Jvm.initJvmState [] (.i32 0) hp jh) = some (.unit, endSt) ∧
                |      endSt.jvmHeap = jh.setStatic "com/alexvanyo/composelife/algorithm/HashLifeComputationKt${'$'}computeLevel4NextGeneration${'$'}1"
                |        "INSTANCE" (.allocRef HashLifeComputation.lambdaClass1) ∧ endSt.heap = hp) ∧
                |    ∃ r : UInt32,
                |      (∃ endSt, Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) 6
                |          Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog
                |          (Jvm.initJvmState [(0, .allocRef HashLifeComputation.lambdaClass1), (1, .boxedULong w)]
                |            (.i32 0) hp jh) = some (.boxedInt r, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      r.toBitVec.getLsbD (Algorithm.mortonIndex4 (x - 2).toNat (y - 2).toNat) =
                |        Algorithm.nextGenAt (Algorithm.leafAt w) x y := by
                |  have h1 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog =
                |      Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog :=
                |    rfl
                |  have h2 : Algorithm.RealJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog = Algorithm.KotlinJvmBytecode.HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog := rfl
                |  rw [h1, h2]
                |  exact ⟨clinit_HashLifeComputationKt_computeLevel4NextGeneration_1_equiv resolveProg hinit d subFuel 5
                |      (Nat.le_refl _) jh hp,
                |    _, invoke_1_equiv resolveProg hr d subFuel 6 hd hsf (Nat.le_refl _) w jh hp hqi hng,
                |    computeNextGenerationPureKotlinModel_correct w x y hx hy⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/algorithm/HashLifeComputationKt.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/algorithm/HashLifeComputationKt\$computeLevel4NextGeneration\$1.class",
                "com/alexvanyo/composelife/algorithm/HashLifeComputationKt\$computeLevel4NextGeneration\$2.class",
            ),
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Algorithm.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "HashLifeComputationKt_computeNextGeneration_prog",
                "HashLifeComputationKt_computeNextGeneration_1_prog",
                "HashLifeComputationKt_packLeafNode_prog",
                "HashLifeComputationKt_LeafNode_prog",
                "HashLifeComputationKt_getNw_prog",
                "HashLifeComputationKt_getNe_prog",
                "HashLifeComputationKt_getSw_prog",
                "HashLifeComputationKt_getSe_prog",
                "HashLifeComputationKt_centeredSubnodeLevel3_prog",
                "HashLifeComputationKt_centeredHorizontalSubnodeLevel3_prog",
                "HashLifeComputationKt_centeredVerticalSubnodeLevel3_prog",
                "HashLifeComputationKt_centeredSubSubnodeLevel4_prog",
                "HashLifeComputationKt_centeredSubSubnodeLevel4_1_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_qFGr5tM_default_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_1_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_default_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_1_invoke_1_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_2_invoke_1_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_1_clinit_prog",
                "HashLifeComputationKt_computeLevel4NextGeneration_2_clinit_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.BitComputationModel",
                "models.HashLifeComputationModel",
                "theorems.BitComputationModelTheorems",
                "theorems.HashLifeComputationModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.HashLifeComputation",
            ),
            defaultOpens = listOf(
                "Algorithm.JvmVerification",
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

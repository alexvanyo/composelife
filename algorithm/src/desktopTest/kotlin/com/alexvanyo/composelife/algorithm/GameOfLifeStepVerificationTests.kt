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
 * Standard `@Test` suite verifying hand-written Kotlin code in `GameOfLifeStep.kt` by lifting the actual compiled
 * `GameOfLifeStepKt.class` JVM bytecode from the test runtime classpath into Lean 4 and proving theorems about that
 * real bytecode with `lake env lean`.
 */
class GameOfLifeStepVerificationTests {
    @Test
    fun stepGeneration_bytecode_implements_conways_game_of_life() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_stepGeneration_implements_conway",
            leanBody = """
                |theorem real_stepGeneration_implements_conway
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
                |    (alive : List (Int32 × Int32)) (hnd : alive.Nodup) (h9 : 9 * alive.length < 2 ^ 32)
                |    (hf : 2000 * (alive.length + 1) ≤ fuel) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
                |    (s sa : Nat) (scls sec : String) (hs : GolStep.IsColl jh s scls sa sec alive)
                |    (hscls : scls = "java/util/Set" ∨ scls = "java/util/LinkedHashSet") :
                |    ∃ r ra endSt, ∃ next : List (Int32 × Int32),
                |      Jvm.runJvmRes (mkAlgKotlinHooks resolveProg d subFuel) fuel
                |          Algorithm.RealJvmBytecode.GameOfLifeStepKt_stepGeneration_prog
                |          (Jvm.initJvmState [(0, .heapRef s)] (.i32 0) hp jh) = some (.heapRef r, endSt) ∧
                |      GolStep.IsColl endSt.jvmHeap r "java/util/LinkedHashSet" ra "java/lang/Object" next ∧
                |      next.Nodup ∧
                |      (∀ c, c ∈ next ↔
                |        Algorithm.nextGenAt (fun x y => decide ((Int32.ofInt x, Int32.ofInt y) ∈ alive))
                |          c.1.toInt c.2.toInt = true) ∧
                |      (∀ c, c ∈ next ↔
                |        neighborCountCoords alive c = 3 ∨ (neighborCountCoords alive c = 2 ∧ c ∈ alive)) ∧
                |      GolStep.Frame jh endSt.jvmHeap ∧ endSt.heap = hp := by
                |  have hprog : Algorithm.RealJvmBytecode.GameOfLifeStepKt_stepGeneration_prog =
                |      Algorithm.KotlinJvmBytecode.GameOfLifeStepKt_stepGeneration_prog := rfl
                |  rw [hprog]
                |  obtain ⟨r, ra, endSt, hrun, hcoll, hframe, hheap⟩ :=
                |    stepGeneration_equiv resolveProg d subFuel fuel alive hnd h9 hf jh hp s sa scls sec hs hscls
                |  exact ⟨r, ra, endSt, stepGenerationModel alive, hrun, hcoll, GolStep.stepGenerationModel_nodup alive,
                |    fun c => mem_stepGenerationModel_iff_nextGenAt alive c,
                |    fun c => stepGenerationModel_conway_iff alive c, hframe, hheap⟩
            """.trimMargin(),
        )
    }

    @Test
    fun stepGenerations_bytecode_iterates_stepGeneration() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_stepGenerations_iterates_stepGeneration",
            leanBody = """
                |theorem real_stepGenerations_iterates_stepGeneration
                |    (d subFuel fuel : Nat) (alive : List (Int32 × Int32)) (step : Int32) (hnd : alive.Nodup)
                |    (P : Nat) (hP : ∀ j < step.toInt.toNat, (stepGenerationsLoop j alive).length ≤ P)
                |    (h9 : 9 * P < 2 ^ 32) (hsf : 2000 * (P + 1) ≤ subFuel) (hf : 14 * step.toInt.toNat + 8 ≤ fuel)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (s sa : Nat) (scls sec : String)
                |    (hs : GolStep.IsColl jh s scls sa sec alive)
                |    (hscls : scls = "java/util/Set" ∨ scls = "java/util/LinkedHashSet") :
                |    ∃ r rcls ra rec endSt,
                |      Jvm.runJvmRes (mkAlgKotlinHooks algKotlinProgLookup (d + 1) subFuel) fuel
                |          Algorithm.RealJvmBytecode.GameOfLifeStepKt_stepGenerations_prog
                |          (Jvm.initJvmState [(0, .heapRef s), (1, .i32 step.toUInt32)] (.i32 0) hp jh) =
                |        some (.heapRef r, endSt) ∧
                |      GolStep.IsColl endSt.jvmHeap r rcls ra rec (stepGenerationsModel alive step) ∧
                |      (step.toInt ≤ 0 → stepGenerationsModel alive step = alive) ∧
                |      (0 < step.toInt → stepGenerationsModel alive step =
                |        stepGenerationsModel (stepGenerationModel alive) (step - 1)) ∧
                |      GolStep.Frame jh endSt.jvmHeap ∧ endSt.heap = hp := by
                |  have hprog : Algorithm.RealJvmBytecode.GameOfLifeStepKt_stepGenerations_prog =
                |      Algorithm.KotlinJvmBytecode.GameOfLifeStepKt_stepGenerations_prog := rfl
                |  rw [hprog]
                |  obtain ⟨r, rcls, ra, rec, endSt, hrun, hcoll, hframe, hheap⟩ :=
                |    stepGenerations_equiv algKotlinProgLookup GolStep.algKotlinProgLookup_stepGeneration d subFuel
                |      fuel alive step hnd P hP h9 hsf hf jh hp s sa scls sec hs hscls
                |  exact ⟨r, rcls, ra, rec, endSt, hrun, hcoll, stepGenerationsModel_nonpositive alive step,
                |    stepGenerationsModel_pos alive step, hframe, hheap⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/algorithm/GameOfLifeStepKt.class",
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Algorithm.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "GameOfLifeStepKt_stepGeneration_prog",
                "GameOfLifeStepKt_stepGenerations_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.GameOfLifeStepModel",
                "theorems.GameOfLifeStepModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.GameOfLifeStep",
            ),
            defaultOpens = listOf(
                "Algorithm.JvmVerification",
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

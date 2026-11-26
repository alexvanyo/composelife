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

package com.alexvanyo.composelife.model

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying `CellState.kt` (`CellState`, `CellStateKt`, `CellStateImpl`)
 * against its live compiled JVM bytecode lifted into Lean 4.
 */
class CellStateVerificationTests {
    @Test
    fun cellState_operations_and_boundingBox_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cellState_ops",
            leanBody = """
                |theorem real_cellState_ops (p d : UInt64) :
                |    (let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
                |     let (c1, h1) := h0.alloc (.instance "com/alexvanyo/composelife/model/CellStateImpl"
                |       [("aliveCells", .heapRef s1)])
                |     ∃ csAddr resSet endSt,
                |       Jvm.runJvmRes cellStateHooks 120 Algorithm.RealJvmBytecode.CellState_offsetBy_prog
                |         (Jvm.initJvmState [(0, .heapRef c1), (1, .i64 d)] (.i32 0) () h1) =
                |         some (.heapRef csAddr, endSt) ∧
                |       csGetField? endSt.jvmHeap csAddr "com/alexvanyo/composelife/model/CellStateImpl" "aliveCells" =
                |         some (.heapRef resSet) ∧
                |       getCsCol? endSt.jvmHeap resSet = some #[.boxedLong (addCellOffset p d)]) ∧
                |    (let (s1, h0) := allocCsCol {} "java/util/Set" #[]
                |     let (c1, h1) := h0.alloc (.instance "com/alexvanyo/composelife/model/CellStateImpl"
                |       [("aliveCells", .heapRef s1)])
                |     ∃ rectAddr endSt,
                |       Jvm.runJvmRes cellStateHooks 40 Algorithm.RealJvmBytecode.CellState_getBoundingBox_prog
                |         (Jvm.initJvmState [(0, .heapRef c1)] (.i32 0) () h1) = some (.heapRef rectAddr, endSt) ∧
                |       csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "left" = some (.i32 0)) := by
                |  refine ⟨?_, ?_⟩
                |  · rw [show Algorithm.RealJvmBytecode.CellState_offsetBy_prog =
                |        Algorithm.KotlinJvmBytecode.CellState_offsetBy_prog from rfl]
                |    exact cellState_offsetBy_singleton_equiv p d
                |  · rw [show Algorithm.RealJvmBytecode.CellState_getBoundingBox_prog =
                |        Algorithm.KotlinJvmBytecode.CellState_getBoundingBox_prog from rfl]
                |    rcases cellState_getBoundingBox_empty_equiv with ⟨r, e, hrun, hl, _⟩
                |    exact ⟨r, e, hrun, hl⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/model/CellState.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/model/CellStateKt.class",
                "com/alexvanyo/composelife/model/CellStateImpl.class",
            ),
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Jvm.JvmInstr",
            requiredProgs = listOf(
                "CellState_offsetBy_prog",
                "CellState_getBoundingBox_prog",
                "CellState_withCell_prog",
                "CellState_equals_prog",
                "CellStateKt_equalsModuloOffset_prog",
            ),
            defaultImports = listOf(
                "models.CellStateModel",
                "theorems.CellStateModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.CellState",
            ),
            defaultOpens = listOf(
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

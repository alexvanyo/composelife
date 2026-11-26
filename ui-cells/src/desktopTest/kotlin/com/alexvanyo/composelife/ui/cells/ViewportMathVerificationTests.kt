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

package com.alexvanyo.composelife.ui.cells

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying `GridDraggableAnchors2d`, `MutableCellWindowViewportStateImpl`,
 * and `TrackingCellWindowViewportState` against their live compiled JVM bytecode lifted into Lean 4.
 */
class ViewportMathVerificationTests {
    @Test
    fun setScaleRange_rejects_empty_new_range_and_clamps_scale_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_setScaleRange_bugfix_and_clamp",
            leanBody = """
                |theorem real_setScaleRange_bugfix_and_clamp (x : Float32) :
                |    (let (oldR, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
                |     let (newR, h1) := allocFloatRange h0 (2.0 : Float32) (0.5 : Float32)
                |     let (rDel, h2) := allocMutableState h1 (.heapRef oldR)
                |     let (sDel, h3) := allocMutableFloatState h2 (1.0 : Float32)
                |     let (selfAddr, h4) := h3.alloc (.instance
                |       "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl"
                |       [("_scaleRange${'$'}delegate", .heapRef rDel), ("_scale${'$'}delegate", .heapRef sDel)])
                |     Jvm.runJvm viewportHooks 40
                |       UiCells.RealJvmBytecode.MutableCellWindowViewportStateImpl_setScaleRange_prog
                |       (initJvmState [(0, .heapRef selfAddr), (1, .heapRef newR)] h4) = none) ∧
                |    (let (rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
                |     let (rDel, h1) := allocMutableState h0 (.heapRef rAddr)
                |     let (sDel, h2) := allocMutableFloatState h1 (1.0 : Float32)
                |     let (selfAddr, h3) := h2.alloc (.instance
                |       "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl"
                |       [("_scaleRange${'$'}delegate", .heapRef rDel), ("_scale${'$'}delegate", .heapRef sDel)])
                |     ∃ endSt,
                |       Jvm.runJvmRes viewportHooks 30
                |         UiCells.RealJvmBytecode.MutableCellWindowViewportStateImpl_setScale_prog
                |         (initJvmState [(0, .heapRef selfAddr), (1, .f32 x)] h3) = some (.unit, endSt) ∧
                |       ucGetField? endSt.jvmHeap sDel "MutableFloatState" "value" =
                |         some (.f32 (coerceInFloatRange x { lo := (0.5 : Float32), hi := (2.0 : Float32) }))) := by
                |  refine ⟨?_, ?_⟩
                |  · rw [show UiCells.RealJvmBytecode.MutableCellWindowViewportStateImpl_setScaleRange_prog =
                |        UiCells.KotlinJvmBytecode.MutableCellWindowViewportStateImpl_setScaleRange_prog from rfl]
                |    exact mutableViewport_setScaleRange_bugfix_equiv.1
                |  · rw [show UiCells.RealJvmBytecode.MutableCellWindowViewportStateImpl_setScale_prog =
                |        UiCells.KotlinJvmBytecode.MutableCellWindowViewportStateImpl_setScale_prog from rfl]
                |    exact mutableViewport_setScale_clamps_equiv x
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "ui-cells",
            classResourcePath = "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d.class",
                "com/alexvanyo/composelife/ui/cells/TrackingCellWindowViewportState.class",
            ),
            realBytecodeNamespace = "UiCells.RealJvmBytecode",
            instrType = "UiCells.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "MutableCellWindowViewportStateImpl_setScaleRange_prog",
                "MutableCellWindowViewportStateImpl_setScale_prog",
                "GridDraggableAnchors2d_positionOf_prog",
                "GridDraggableAnchors2d_closestAnchor_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.ViewportMathModel",
                "theorems.ViewportMathModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.ViewportMath",
            ),
            defaultOpens = listOf(
                "UiCells.JvmVerification",
                "UiCells.Model",
                "UiCells.KotlinJvmVerification",
            ),
        )
    }
}

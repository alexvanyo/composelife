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
 * Standard `@Test` suite verifying `LineSegment.kt` and `LineSegmentPath.kt` against their
 * live compiled JVM bytecode lifted into Lean 4.
 */
class LineSegmentWrapperVerificationTests {
    @Test
    fun lineSegmentPath_and_cellIntersections_guards_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_lineSegment_guards_and_singleton",
            leanBody = """
                |theorem real_lineSegment_guards_and_singleton :
                |    (let (listAddr, h) := allocCollection {} "java/util/List" #[]
                |     Jvm.runJvm lineSegHooks 40 Geometry.RealJvmBytecode.LineSegmentKt_cellIntersections_prog
                |       (initJvmState [(0, .heapRef listAddr)] h) = none) ∧
                |    (let (listAddr, h0) := allocCollection {} "java/util/List" #[]
                |     let (selfAddr, h1) := h0.alloc (.instance "com/alexvanyo/composelife/geometry/LineSegmentPath" [])
                |     Jvm.runJvm lineSegHooks 40 Geometry.RealJvmBytecode.LineSegmentPath_init_prog
                |       (initJvmState [(0, .heapRef selfAddr), (1, .heapRef listAddr)] h1) = none) ∧
                |    (let (listAddr, h) := allocCollection {} "java/util/List" #[.boxedLong 0]
                |     ∃ setAddr endSt,
                |       Jvm.runJvmRes lineSegHooks 80 Geometry.RealJvmBytecode.LineSegmentKt_cellIntersections_prog
                |         (initJvmState [(0, .heapRef listAddr)] h) = some (.heapRef setAddr, endSt) ∧
                |       getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" =
                |         some #[.boxedLong (floorModel 0)]) := by
                |  refine ⟨?_, ?_, ?_⟩
                |  · rw [show Geometry.RealJvmBytecode.LineSegmentKt_cellIntersections_prog =
                |        Geometry.KotlinJvmBytecode.LineSegmentKt_cellIntersections_prog from rfl]
                |    exact lineSegment_cellIntersections_empty_throws
                |  · rw [show Geometry.RealJvmBytecode.LineSegmentPath_init_prog =
                |        Geometry.KotlinJvmBytecode.LineSegmentPath_init_prog from rfl]
                |    exact lineSegmentPath_init_empty_throws
                |  · rw [show Geometry.RealJvmBytecode.LineSegmentKt_cellIntersections_prog =
                |        Geometry.KotlinJvmBytecode.LineSegmentKt_cellIntersections_prog from rfl]
                |    exact lineSegment_cellIntersections_singleton_equiv
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "geometry",
            classResourcePath = "com/alexvanyo/composelife/geometry/LineSegmentKt.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/geometry/LineSegmentPath.class",
                "com/alexvanyo/composelife/geometry/LineSegmentPathKt.class",
            ),
            realBytecodeNamespace = "Geometry.RealJvmBytecode",
            instrType = "Geometry.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "LineSegmentKt_cellIntersections_prog",
                "LineSegmentKt_cellIntersections_1_prog",
                "LineSegmentKt_cellIntersections_2_prog",
                "LineSegmentPath_init_prog",
                "LineSegmentPathKt_cellIntersections_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.GeometryExtensionsModel",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.LineSegmentWrapper",
            ),
            defaultOpens = listOf(
                "Geometry.JvmVerification",
                "Geometry.KotlinModel",
                "Geometry.KotlinJvmVerification",
            ),
        )
    }
}

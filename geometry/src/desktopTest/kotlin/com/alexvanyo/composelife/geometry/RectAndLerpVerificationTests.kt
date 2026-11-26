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
 * Standard `@Test` suite verifying `RectExtensions.kt` and `IntSizeLerp.kt` against their
 * live compiled JVM bytecode lifted into Lean 4.
 */
class RectAndLerpVerificationTests {
    @Test
    fun rect_rtl_ltr_duality_and_scaling_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_rect_rtl_ltr_and_scaling",
            leanBody = """
                |theorem real_rect_rtl_ltr_and_scaling
                |    (rect intRect : RectCorners)
                |    (offsetTimes offsetDiv : UInt64 → Float32 → UInt64)
                |    (lerpInt : Int32 → Int32 → Float32 → Int32)
                |    (scale : Float32) (d : LayoutDirectionModel) :
                |    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 20
                |      Geometry.RealJvmBytecode.RectExtensionsKt_times_prog
                |      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, .f32 scale)]) =
                |      some (.pair (.i64 (offsetTimes rect.topLeft scale))
                |        (.i64 (offsetTimes rect.bottomRight scale))) ∧
                |    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 20
                |      Geometry.RealJvmBytecode.RectExtensionsKt_div_prog
                |      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, .f32 scale)]) =
                |      some (.pair (.i64 (offsetDiv rect.topLeft scale))
                |        (.i64 (offsetDiv rect.bottomRight scale))) ∧
                |    Jvm.runJvm (mkRectLerpHooks rect intRect) 25
                |      Geometry.RealJvmBytecode.RectExtensionsKt_topStart_prog
                |      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d.flip)]
                |        rectWhenMappingsHeap) =
                |      Jvm.runJvm (mkRectLerpHooks rect intRect) 25
                |        Geometry.RealJvmBytecode.RectExtensionsKt_topEnd_prog
                |        (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
                |          rectWhenMappingsHeap) ∧
                |    Jvm.runJvm (mkRectLerpHooks rect intRect) 25
                |      Geometry.RealJvmBytecode.RectExtensionsKt_bottomStart_1_prog
                |      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d.flip)]
                |        rectWhenMappingsHeap) =
                |      Jvm.runJvm (mkRectLerpHooks rect intRect) 25
                |        Geometry.RealJvmBytecode.RectExtensionsKt_bottomEnd_1_prog
                |        (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
                |          rectWhenMappingsHeap) := by
                |  refine ⟨rect_times_equiv rect intRect offsetTimes offsetDiv lerpInt scale,
                |    rect_div_equiv rect intRect offsetTimes offsetDiv lerpInt scale, ?_, ?_⟩
                |  · rw [show Geometry.RealJvmBytecode.RectExtensionsKt_topStart_prog =
                |        Geometry.KotlinJvmBytecode.RectExtensionsKt_topStart_prog from rfl,
                |      show Geometry.RealJvmBytecode.RectExtensionsKt_topEnd_prog =
                |        Geometry.KotlinJvmBytecode.RectExtensionsKt_topEnd_prog from rfl,
                |      rect_topStart_equiv, rect_topEnd_equiv, rectCorners_topStart_flip]
                |  · rw [show Geometry.RealJvmBytecode.RectExtensionsKt_bottomStart_1_prog =
                |        Geometry.KotlinJvmBytecode.RectExtensionsKt_bottomStart_1_prog from rfl,
                |      show Geometry.RealJvmBytecode.RectExtensionsKt_bottomEnd_1_prog =
                |        Geometry.KotlinJvmBytecode.RectExtensionsKt_bottomEnd_1_prog from rfl,
                |      intRect_bottomStart_equiv, intRect_bottomEnd_equiv, rectCorners_bottomStart_flip]
            """.trimMargin(),
        )
    }

    @Test
    fun intSize_lerp_bytecode_roundtrip_and_endpoints() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_intSize_lerp_endpoints",
            leanBody = """
                |theorem real_intSize_lerp_endpoints
                |    (rect intRect : RectCorners)
                |    (offsetTimes offsetDiv : UInt64 → Float32 → UInt64)
                |    (lerpInt : Int32 → Int32 → Float32 → Int32)
                |    (h0 : ∀ a b, lerpInt a b (0.0 : Float32) = a)
                |    (h1 : ∀ a b, lerpInt a b (1.0 : Float32) = b)
                |    (start stop : UInt64) :
                |    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 90
                |      Geometry.RealJvmBytecode.IntSizeLerpKt_lerp_prog
                |      (initJvmState [(0, .i64 start), (2, .i64 stop), (4, .f32 0.0)]) = some (.i64 start) ∧
                |    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 90
                |      Geometry.RealJvmBytecode.IntSizeLerpKt_lerp_prog
                |      (initJvmState [(0, .i64 start), (2, .i64 stop), (4, .f32 1.0)]) = some (.i64 stop) := by
                |  have hprog : Geometry.RealJvmBytecode.IntSizeLerpKt_lerp_prog =
                |      Geometry.KotlinJvmBytecode.IntSizeLerpKt_lerp_prog := rfl
                |  rw [hprog, intSize_lerp_equiv, intSize_lerp_equiv]
                |  have hend := lerpIntSize_endpoints lerpInt h0 h1 start stop
                |  rw [hend.1, hend.2]
                |  exact ⟨rfl, rfl⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "geometry",
            classResourcePath = "com/alexvanyo/composelife/geometry/RectExtensionsKt.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/geometry/IntSizeLerpKt.class",
            ),
            realBytecodeNamespace = "Geometry.RealJvmBytecode",
            instrType = "Geometry.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "RectExtensionsKt_times_prog",
                "RectExtensionsKt_div_prog",
                "RectExtensionsKt_topStart_prog",
                "RectExtensionsKt_topEnd_prog",
                "RectExtensionsKt_bottomStart_1_prog",
                "RectExtensionsKt_bottomEnd_1_prog",
                "IntSizeLerpKt_lerp_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.RectAndLerpModel",
                "theorems.RectAndLerpModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.RectAndLerp",
            ),
            defaultOpens = listOf(
                "Geometry.JvmVerification",
                "Geometry.KotlinModel",
                "Geometry.KotlinJvmVerification",
            ),
        )
    }
}

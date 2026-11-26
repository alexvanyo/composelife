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
 * Standard `@Test` suite verifying `ColorComponent.kt` ARGB bit-packing and lens laws against
 * its live compiled JVM bytecode lifted into Lean 4.
 */
class ColorComponentVerificationTests {
    @Test
    fun colorComponent_lens_and_argb_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_colorComponent_lens",
            leanBody = """
                |theorem real_colorComponent_lens (argb v : UInt32) (c : RgbComponent) :
                |    Jvm.runJvm colorCompHooks 40 UiCommon.RealJvmBytecode.ColorComponentKt_get_prog
                |      (Jvm.initJvmState [(0, .i64 argb.toUInt64), (2, rgbCompVal c)] (.i32 0) () {}) =
                |      some (.i32 (getColorComponent argb c)) ∧
                |    Jvm.runJvm colorCompHooks 60 UiCommon.RealJvmBytecode.ColorComponentKt_withComponent_prog
                |      (Jvm.initJvmState [(0, .i64 argb.toUInt64), (2, rgbCompVal c), (3, .i32 v)] (.i32 0) () {}) =
                |      some (.i64 (withColorComponent argb c v).toUInt64) ∧
                |    getColorComponent (withColorComponent argb c v) c = v &&& 255 ∧
                |    argbAlpha (withColorComponent argb c v) = argbAlpha argb := by
                |  refine ⟨?_, ?_, withColorComponent_get_same argb c v,
                |    withColorComponent_preserves_alpha argb c v⟩
                |  · rw [show UiCommon.RealJvmBytecode.ColorComponentKt_get_prog =
                |        UiCommon.KotlinJvmBytecode.ColorComponentKt_get_prog from rfl]
                |    exact colorComponent_get_equiv argb c
                |  · rw [show UiCommon.RealJvmBytecode.ColorComponentKt_withComponent_prog =
                |        UiCommon.KotlinJvmBytecode.ColorComponentKt_withComponent_prog from rfl]
                |    exact colorComponent_withComponent_equiv argb c v
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "ui-common",
            classResourcePath = "com/alexvanyo/composelife/ui/util/ColorComponentKt.class",
            realBytecodeNamespace = "UiCommon.RealJvmBytecode",
            instrType = "Jvm.JvmInstr",
            requiredProgs = listOf(
                "ColorComponentKt_getAlpha_prog",
                "ColorComponentKt_getRed_prog",
                "ColorComponentKt_getGreen_prog",
                "ColorComponentKt_getBlue_prog",
                "ColorComponentKt_get_prog",
                "ColorComponentKt_withComponent_prog",
            ),
            defaultImports = listOf(
                "models.ColorComponentModel",
                "theorems.ColorComponentModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.ColorComponent",
            ),
            defaultOpens = listOf(
                "UiCommon.KotlinModel",
                "UiCommon.KotlinJvmVerification",
            ),
        )
    }
}

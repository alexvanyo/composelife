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
 * Standard `@Test` suite verifying `WindowInsetsLerp.kt`, `PaddingValuesExtensions.kt`,
 * `NonNegativeLong.kt`, and `NonNegativeDouble.kt` against their live compiled JVM bytecode.
 */
class UiUtilVerificationTests {
    @Test
    fun nonNegativeDouble_rejects_nan_and_negative_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_nonNegativeDouble_nan_guard",
            leanBody = """
                |theorem real_nonNegativeDouble_nan_guard :
                |    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc
                |       (.instance "TextFieldBuffer" [("text", .str "NaN"), ("reverted", .i32 0)])
                |     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseDouble := fun _ => some (0.0 / 0.0))) 50
                |       UiCommon.RealJvmBytecode.NonNegativeDouble_transformInput_prog
                |       (Jvm.initJvmState [(0, .allocRef "com/alexvanyo/composelife/ui/util/NonNegativeDouble"),
                |         (1, .heapRef buf)] (.i32 0) () h) = some (.unit, endSt) ∧
                |       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 1)) ∧
                |    (let (buf, h) := ({} : Jvm.JvmHeap Empty).alloc
                |       (.instance "TextFieldBuffer" [("text", .str "3.5"), ("reverted", .i32 0)])
                |     ∃ endSt, Jvm.runJvmRes (mkUiUtilHooks (parseDouble := fun _ => some 3.5)) 50
                |       UiCommon.RealJvmBytecode.NonNegativeDouble_transformInput_prog
                |       (Jvm.initJvmState [(0, .allocRef "com/alexvanyo/composelife/ui/util/NonNegativeDouble"),
                |         (1, .heapRef buf)] (.i32 0) () h) = some (.unit, endSt) ∧
                |       utilGetField? endSt.jvmHeap buf "TextFieldBuffer" "reverted" = some (.i32 0)) := by
                |  rw [show UiCommon.RealJvmBytecode.NonNegativeDouble_transformInput_prog =
                |      UiCommon.KotlinJvmBytecode.NonNegativeDouble_transformInput_prog from rfl]
                |  exact ⟨nonNegativeDouble_transformInput_equiv.2.1, nonNegativeDouble_transformInput_equiv.2.2.2⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "ui-common",
            classResourcePath = "com/alexvanyo/composelife/ui/util/NonNegativeDouble.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/ui/util/NonNegativeLong.class",
                "com/alexvanyo/composelife/ui/util/WindowInsetsLerpKt.class",
                "com/alexvanyo/composelife/ui/util/WindowInsetsLerpKt\$lerp\$1.class",
                "com/alexvanyo/composelife/ui/util/PaddingValuesExtensionsKt.class",
                "com/alexvanyo/composelife/ui/util/PaddingValuesExtensionsKt\$plus\$1.class",
            ),
            realBytecodeNamespace = "UiCommon.RealJvmBytecode",
            instrType = "Jvm.JvmInstr",
            requiredProgs = listOf(
                "NonNegativeDouble_transformInput_prog",
                "NonNegativeLong_transformInput_prog",
                "WindowInsetsLerpKt_lerp_1_getLeft_prog",
                "PaddingValuesExtensionsKt_plus_1_calculateTopPadding_prog",
            ),
            defaultImports = listOf(
                "models.UiUtilModel",
                "theorems.UiUtilModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.UiUtil",
            ),
            defaultOpens = listOf(
                "UiCommon.KotlinModel",
                "UiCommon.KotlinJvmVerification",
            ),
        )
    }
}

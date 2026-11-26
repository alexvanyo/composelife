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
 * Standard `@Test` suite verifying `DeserializationResult.kt` and `CellStateFormat.kt` against
 * their live compiled JVM bytecode lifted into Lean 4.
 */
class DeserializationResultVerificationTests {
    @Test
    fun deserializationResult_and_format_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_deser_and_format_semantics",
            leanBody = """
                |theorem real_deser_and_format_semantics (a b : DeserResultModel) :
                |    (let (addr, h) := allocDeserResult {} a
                |     Jvm.runJvm deserHooks 30 Algorithm.RealJvmBytecode.DeserializationResultKt_isSuccessful_prog
                |       (Jvm.initJvmState [(0, .heapRef addr)] (.i32 0) () h) =
                |       some (.i32 (if a.isSuccessful then 1 else 0))) ∧
                |    (let (a0, h0) := allocDeserResult {} a
                |     let (a1, h1) := allocDeserResult h0 b
                |     let (listAddr, h2) := h1.alloc (.objArray "java/lang/Iterable" #[.heapRef a0, .heapRef a1])
                |     Jvm.runJvm deserHooks 120 Algorithm.RealJvmBytecode.DeserializationResultKt_reduceToSuccessful_prog
                |       (Jvm.initJvmState [(0, .heapRef listAddr)] (.i32 0) () h2) =
                |       some (.heapRef (if reduceToSuccessfulPicksFirst a b then a0 else a1))) ∧
                |    Jvm.runJvm deserHooks 40 Algorithm.RealJvmBytecode.CellStateFormatKt_fromFileExtension_prog
                |      (Jvm.initJvmState [(0, .allocRef "Companion"), (1, .str "rle")] (.i32 0) () {}) =
                |      some (formatVal .runLengthEncoding) := by
                |  refine ⟨?_, ?_, ?_⟩
                |  · rw [show Algorithm.RealJvmBytecode.DeserializationResultKt_isSuccessful_prog =
                |        Algorithm.KotlinJvmBytecode.DeserializationResultKt_isSuccessful_prog from rfl]
                |    exact deserializationResult_isSuccessful_equiv a
                |  · rw [show Algorithm.RealJvmBytecode.DeserializationResultKt_reduceToSuccessful_prog =
                |        Algorithm.KotlinJvmBytecode.DeserializationResultKt_reduceToSuccessful_prog from rfl]
                |    exact deserializationResult_reduceToSuccessful_pair_equiv a b
                |  · rw [show Algorithm.RealJvmBytecode.CellStateFormatKt_fromFileExtension_prog =
                |        Algorithm.KotlinJvmBytecode.CellStateFormatKt_fromFileExtension_prog from rfl]
                |    exact cellStateFormat_fromFileExtension_known_equiv.2.2.2.1
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/model/DeserializationResultKt.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/model/CellStateFormatKt.class",
            ),
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Jvm.JvmInstr",
            requiredProgs = listOf(
                "DeserializationResultKt_isSuccessful_prog",
                "DeserializationResultKt_reduceToSuccessful_prog",
                "CellStateFormatKt_fromFileExtension_prog",
            ),
            defaultImports = listOf(
                "models.DeserializationResultModel",
                "theorems.DeserializationResultModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.DeserializationResult",
            ),
            defaultOpens = listOf(
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

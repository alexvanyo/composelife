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
 * Standard `@Test` suite verifying `HashLifeCache.kt` (`Cache`, `Equivalence.Wrapper`,
 * `FixedWrapper`, `ReusableWrapper`) against its live compiled JVM bytecode lifted into Lean 4.
 */
class HashLifeCacheVerificationTests {
    @Test
    fun cache_and_equivalence_wrapper_bytecode() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cache_and_wrapper_semantics",
            leanBody = """
                |theorem real_cache_and_wrapper_semantics (k : String) (gen : UInt64) :
                |    (let (mAddr, h0) := allocMap {} #[]
                |     let (gAddr, h1) := allocMap h0 #[]
                |     let (selfAddr, h2) := h1.alloc (.instance "com/alexvanyo/composelife/algorithm/Cache"
                |       [("load", .allocRef "load"), ("getGenerationIndex", .allocRef "getGen"),
                |        ("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
                |     ∃ endSt,
                |       Jvm.runJvmRes (mkCacheHooks (genIndex := gen)) 60 Algorithm.RealJvmBytecode.Cache_get_prog
                |         (Jvm.initJvmState [(0, .heapRef selfAddr), (1, .str k)] (.i32 0) () h2) =
                |         some (.str ("loaded:" ++ k), endSt) ∧
                |       getMapEntries? endSt.jvmHeap mAddr = some #[.pair (.str k) (.str ("loaded:" ++ k))] ∧
                |       getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str k) (.boxedLong gen)]) ∧
                |    (let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc
                |       (.instance "com/alexvanyo/composelife/algorithm/Equivalence${'$'}ReusableWrapper" [("_value", .null)])
                |     Jvm.runJvm cacheHooks 30 Algorithm.RealJvmBytecode.Equivalence_ReusableWrapper_getValue_prog
                |       (Jvm.initJvmState [(0, .heapRef selfAddr)] (.i32 0) () h) = none) := by
                |  refine ⟨?_, ?_⟩
                |  · rw [show Algorithm.RealJvmBytecode.Cache_get_prog =
                |        Algorithm.KotlinJvmBytecode.Cache_get_prog from rfl]
                |    exact cache_get_miss_equiv (fun s => "loaded:" ++ s) gen k
                |  · rw [show Algorithm.RealJvmBytecode.Equivalence_ReusableWrapper_getValue_prog =
                |        Algorithm.KotlinJvmBytecode.Equivalence_ReusableWrapper_getValue_prog from rfl]
                |    exact equivalence_reusableWrapper_getValue_uninit_throws
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/algorithm/Cache.class",
            extraClassResourcePaths = listOf(
                "com/alexvanyo/composelife/algorithm/Equivalence\$Wrapper.class",
                "com/alexvanyo/composelife/algorithm/Equivalence\$FixedWrapper.class",
                "com/alexvanyo/composelife/algorithm/Equivalence\$ReusableWrapper.class",
            ),
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Jvm.JvmInstr",
            requiredProgs = listOf(
                "Cache_get_prog",
                "Cache_getWithQuery_prog",
                "Cache_prune_prog",
                "Equivalence_Wrapper_equals_prog",
                "Equivalence_ReusableWrapper_getValue_prog",
            ),
            defaultImports = listOf(
                "models.HashLifeCacheModel",
                "theorems.HashLifeCacheModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.HashLifeCache",
            ),
            defaultOpens = listOf(
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}

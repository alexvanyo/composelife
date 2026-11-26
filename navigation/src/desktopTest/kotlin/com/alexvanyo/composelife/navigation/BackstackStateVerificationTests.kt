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

package com.alexvanyo.composelife.navigation

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue
import kotlin.uuid.Uuid

class BackstackStateVerificationTests {
    private val entryVerificationSpec = JvmBytecodeVerificationSpec(
        moduleDirName = "navigation",
        classResourcePath = "com/alexvanyo/composelife/navigation/BackstackEntry.class",
        semanticsImport = "JvmSemantics",
        realBytecodeNamespace = "Navigation.RealJvmBytecode",
        instrType = "Navigation.JvmVerification.JvmInstr",
        requiredProgs = listOf(
            "BackstackEntry_init_prog",
            "BackstackEntry_getValue_prog",
            "BackstackEntry_getPrevious_prog",
            "BackstackEntry_getId_prog",
        ),
        defaultImports = listOf(
            "models.BackstackStateModel",
            "theorems.BackstackStateModelTheorems",
            "proofs.KotlinJvmEquiv.BackstackState",
        ),
        defaultOpens = listOf(
            "Navigation",
            "Navigation.KotlinModel",
            "Navigation.KotlinJvmVerification",
        ),
    )

    @Test
    fun verifyBackstackStateModelAgainstLiveBytecode() {
        entryVerificationSpec.verifyTheorem(
            ownerClass = BackstackStateVerificationTests::class.java,
            theoremName = "live_backstackEntry_verified",
            leanBody = """
                theorem live_backstackEntry_verified (val prev : Jvm.JvmVal Empty) (id : String) :
                    let (addr, h0) := ({} : Jvm.JvmHeap Empty).alloc
                      (.instance "com/alexvanyo/composelife/navigation/BackstackEntry"
                        [("value", val), ("previous", prev), ("id", .str id)])
                    Jvm.runJvm bsHooks 10 RealJvmBytecode.BackstackEntry_getId_prog
                      (Jvm.initJvmState [(0, .heapRef addr)] (.i32 0) () h0) = some (.str id) := by
                  rw [show RealJvmBytecode.BackstackEntry_getId_prog =
                    KotlinJvmBytecode.BackstackEntry_getId_prog from rfl]
                  exact backstackEntry_getId_equiv val prev id
            """.trimIndent(),
        )
    }

    @Test
    fun backstackEntryIterationAndPreviousMatchVerifiedModel() {
        val root = BackstackEntry(value = "root", previous = null)
        val child = BackstackEntry(value = "child", previous = root)
        val entries = child.iterator().asSequence().toList()
        assertEquals(listOf(child, root), entries)

        val map = mutableMapOf(root.id to root, child.id to child)
        val controller = object : MutableBackstackNavigationController<String> {
            override val entryMap = map
            override var currentEntryId: Uuid = child.id
        }

        assertTrue(controller.canNavigateBack)
        assertEquals(root.id, controller.previousEntryId)
        assertEquals(root, controller.previousEntry)

        assertTrue(controller.withExpectedActor(null) { /* no-op */ })
        assertTrue(controller.withExpectedActor(child.id) { /* no-op */ })
        assertFalse(controller.withExpectedActor(root.id) { /* no-op */ })

        controller.popBackstack()
        assertFalse(controller.canNavigateBack)
        assertNull(controller.previousEntryId)
        assertNull(controller.previousEntry)
    }
}

/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.kmpstaterestorationtester

import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.LocalSaveableStateRegistry
import androidx.compose.runtime.saveable.SaveableStateRegistry
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.RetainedStateRegistry

/**
 * Helps to test the state restoration for your Composable component.
 *
 * Instead of calling [ComposeUiTest.setContent] you need to use [setContent] on this
 * object, then change your state so there is some change to be restored, then execute
 * [emulateSavedInstanceStateRestore] and assert your state is restored properly.
 *
 * Note that this tests only the restoration of the local state of the composable you passed to
 * [setContent] and useful for testing [androidx.compose.runtime.saveable.rememberSaveable]
 * integration. It is not testing the integration with any other life cycles or Activity callbacks.
 */
@OptIn(ExperimentalTestApi::class)
class KmpStateRestorationTester(private val composeUiTest: ComposeUiTest) {

    private var registry: RestorationRegistry? = null

    /**
     * This functions is a direct replacement for [ComposeUiTest.setContent] if you are
     * going to use [emulateSavedInstanceStateRestore] in the test.
     */
    fun setContent(composable: @Composable () -> Unit) {
        composeUiTest.setContent {
            // If there is no current saveable state registry, add one that can save anything for multiplatform use.
            val currentSaveableStateRegistry = LocalSaveableStateRegistry.current
            val resolvedSaveableStateRegistry = currentSaveableStateRegistry ?: SaveableStateRegistry(null) { true }
            CompositionLocalProvider(
                LocalSaveableStateRegistry provides resolvedSaveableStateRegistry,
                // Replace the default NoOpRetainedStateRegistry with one that will save.
                LocalRetainedStateRegistry provides remember { RetainedStateRegistry() },
            ) {
                InjectRestorationRegistry { registry ->
                    this.registry = registry
                    composable()
                }
            }
        }
    }

    /**
     * Saves all the state stored via [savedInstanceState] or [rememberSaveable],
     * disposes current composition, and composes again the content passed to [setContent].
     * Allows to test how your component behaves when the state restoration is happening.
     * Note that the state stored via regular state() or remember() will be lost.
     */
    fun emulateSavedInstanceStateRestore() {
        val registry = checkNotNull(registry) {
            "setContent should be called first!"
        }
        composeUiTest.runOnIdle {
            registry.saveStateAndDisposeChildren()
        }
        composeUiTest.runOnIdle {
            registry.emitChildrenWithRestoredState()
        }
        composeUiTest.runOnIdle {
            // we just wait for the children to be emitted
        }
    }

    @Composable
    private fun InjectRestorationRegistry(content: @Composable (RestorationRegistry) -> Unit) {
        val originalSaveableStateRegistry = requireNotNull(LocalSaveableStateRegistry.current) {
            "StateRestorationTester requires composeTestRule.setContent() to provide " +
                "a SaveableStateRegistry implementation via LocalSaveableStateRegistry"
        }
        val originalRetainedStateRegistry = LocalRetainedStateRegistry.current
        val restorationRegistry = remember {
            RestorationRegistry(originalSaveableStateRegistry, originalRetainedStateRegistry)
        }
        CompositionLocalProvider(
            LocalSaveableStateRegistry provides restorationRegistry,
            LocalRetainedStateRegistry provides restorationRegistry,
        ) {
            if (restorationRegistry.shouldEmitChildren) {
                content(restorationRegistry)
            }
        }
    }
}

internal interface RestorationRegistry : SaveableStateRegistry, RetainedStateRegistry {
    val shouldEmitChildren: Boolean

    fun saveStateAndDisposeChildren()

    fun emitChildrenWithRestoredState()
}

internal expect fun RestorationRegistry(
    originalSaveableStateRegistry: SaveableStateRegistry,
    originalRetainedStateRegistry: RetainedStateRegistry,
): RestorationRegistry

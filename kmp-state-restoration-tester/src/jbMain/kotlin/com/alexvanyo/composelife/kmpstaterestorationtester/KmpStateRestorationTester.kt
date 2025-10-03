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
import androidx.compose.runtime.remember
import androidx.compose.runtime.retain.ControlledRetainScope
import androidx.compose.runtime.retain.LocalRetainScope
import androidx.compose.runtime.retain.RetainScope
import androidx.compose.runtime.saveable.LocalSaveableStateRegistry
import androidx.compose.runtime.saveable.SaveableStateRegistry
import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi

/**
 * Helps to test the state restoration for your Composable component.
 *
 * Instead of calling [ComposeUiTest.setContent] you need to use [setContent] on this
 * object, then change your state so there is some change to be restored, then execute
 * [emulateStateRestore] and assert your state is restored properly.
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
     * going to use [emulateStateRestore] in the test.
     */
    fun setContent(composable: @Composable () -> Unit) {
        composeUiTest.setContent {
            // If there is no current saveable state registry, add one that can save anything for multiplatform use.
            val currentSaveableStateRegistry = LocalSaveableStateRegistry.current
            val resolvedSaveableStateRegistry = currentSaveableStateRegistry ?: SaveableStateRegistry(null) { true }
            CompositionLocalProvider(
                LocalSaveableStateRegistry provides resolvedSaveableStateRegistry,
                LocalRetainScope provides remember { ControlledRetainScope() },
            ) {
                InjectRestorationRegistry { registry ->
                    this.registry = registry
                    composable()
                }
            }
        }
    }

    /**
     * Saves all the state stored via [savedInstanceState], [rememberSaveable] and [retain],
     * disposes current composition, and composes again the content passed to [setContent].
     * Allows to test how your component behaves when the state restoration is happening.
     * Note that the state stored via regular state() or remember() will be lost.
     */
    fun emulateStateRestore() {
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
            registry.restorationFinished()
        }
    }

    @Composable
    private fun InjectRestorationRegistry(content: @Composable (RestorationRegistry) -> Unit) {
        val originalSaveableStateRegistry = requireNotNull(LocalSaveableStateRegistry.current) {
            "StateRestorationTester requires composeTestRule.setContent() to provide " +
                "a SaveableStateRegistry implementation via LocalSaveableStateRegistry"
        }
        val originalRetainScope = LocalRetainScope.current
        val restorationRegistry = remember {
            RestorationRegistry(originalSaveableStateRegistry, originalRetainScope as ControlledRetainScope)
        }
        CompositionLocalProvider(
            LocalSaveableStateRegistry provides restorationRegistry,
            LocalRetainScope provides restorationRegistry.retainScope,
        ) {
            if (restorationRegistry.shouldEmitChildren) {
                content(restorationRegistry)
            }
        }
    }
}

internal interface RestorationRegistry : SaveableStateRegistry {
    val retainScope: RetainScope

    val shouldEmitChildren: Boolean

    fun saveStateAndDisposeChildren()

    fun emitChildrenWithRestoredState()

    fun restorationFinished()
}

internal expect fun RestorationRegistry(
    originalSaveableStateRegistry: SaveableStateRegistry,
    originalRetainScope: ControlledRetainScope,
): RestorationRegistry

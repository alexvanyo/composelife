/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.ui.test.ExperimentalTestApi
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.kmpGetEntryPoint
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationEntryPoint
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
class InlineEditPaneStateTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {
    private val entryPoint get() = applicationComponent.kmpGetEntryPoint<TestComposeLifeApplicationEntryPoint>()

    private val cellStateParserProvider: CellStateParserProvider = entryPoint

    @Test
    fun initial_state_is_correct_when_onboarding() = runUiTest { _, composeUiTest ->
        val composeLifePreferences = TestComposeLifePreferences(
            touchToolConfig = ToolConfig.Pan,
            mouseToolConfig = ToolConfig.Select,
            stylusToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = false,
            enableClipboardWatching = true,
        )

        lateinit var inlineEditPaneState: InlineEditPaneState

        composeUiTest.setContent {
            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            val preferences = loadedPreferencesState.value

            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = composeLifePreferences,
                preferences = preferences,
                cellStateParser = cellStateParserProvider.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        assertEquals(
            ToolConfig.Pan,
            inlineEditPaneState.touchToolConfig,
        )
        assertEquals(
            ToolConfig.Draw,
            inlineEditPaneState.stylusToolConfig,
        )
        assertEquals(
            ToolConfig.Select,
            inlineEditPaneState.mouseToolConfig,
        )

        val clipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.Onboarding>(clipboardWatchingState)
    }

    @Test
    fun allowing_clipboard_watching_updates_state_correctly() = runUiTest { _, composeUiTest ->
        val composeLifePreferences = TestComposeLifePreferences(
            touchToolConfig = ToolConfig.Pan,
            mouseToolConfig = ToolConfig.Select,
            stylusToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = false,
            enableClipboardWatching = true,
        )

        lateinit var inlineEditPaneState: InlineEditPaneState

        composeUiTest.setContent {
            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            val preferences = loadedPreferencesState.value

            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = composeLifePreferences,
                preferences = preferences,
                cellStateParser = cellStateParserProvider.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        val initialClipboardWatchingState = inlineEditPaneState.clipboardWatchingState
        assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

        initialClipboardWatchingState.onAllowClipboardWatching()

        composeUiTest.waitForIdle()

        val newPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(newPreferencesState.isSuccess())
        val newPreferences = newPreferencesState.value

        assertTrue(newPreferences.completedClipboardWatchingOnboarding)
        assertTrue(newPreferences.enableClipboardWatching)

        val newClipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingEnabled>(newClipboardWatchingState)
    }

    @Test
    fun disallowing_clipboard_watching_updates_state_correctly() = runUiTest { _, composeUiTest ->
        val composeLifePreferences = TestComposeLifePreferences(
            touchToolConfig = ToolConfig.Pan,
            mouseToolConfig = ToolConfig.Select,
            stylusToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = false,
            enableClipboardWatching = true,
        )

        lateinit var inlineEditPaneState: InlineEditPaneState

        composeUiTest.setContent {
            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            val preferences = loadedPreferencesState.value

            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = composeLifePreferences,
                preferences = preferences,
                cellStateParser = cellStateParserProvider.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        val initialClipboardWatchingState = inlineEditPaneState.clipboardWatchingState
        assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

        initialClipboardWatchingState.onDisallowClipboardWatching()

        composeUiTest.waitForIdle()

        val newPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(newPreferencesState.isSuccess())
        val newPreferences = newPreferencesState.value

        assertTrue(newPreferences.completedClipboardWatchingOnboarding)
        assertFalse(newPreferences.enableClipboardWatching)

        val newClipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingDisabled>(newClipboardWatchingState)
    }

    @Test
    fun initial_state_is_correct_when_clipboard_watching_enabled() = runUiTest { _, composeUiTest ->
        val composeLifePreferences = TestComposeLifePreferences(
            touchToolConfig = ToolConfig.Pan,
            mouseToolConfig = ToolConfig.Select,
            stylusToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = true,
            enableClipboardWatching = true,
        )

        lateinit var inlineEditPaneState: InlineEditPaneState

        composeUiTest.setContent {
            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            val preferences = loadedPreferencesState.value

            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = composeLifePreferences,
                preferences = preferences,
                cellStateParser = cellStateParserProvider.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        assertEquals(
            ToolConfig.Pan,
            inlineEditPaneState.touchToolConfig,
        )
        assertEquals(
            ToolConfig.Draw,
            inlineEditPaneState.stylusToolConfig,
        )
        assertEquals(
            ToolConfig.Select,
            inlineEditPaneState.mouseToolConfig,
        )

        val clipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingEnabled>(clipboardWatchingState)
    }

    @Test
    fun initial_state_is_correct_when_clipboard_watching_disabled() = runUiTest { _, composeUiTest ->
        val composeLifePreferences = TestComposeLifePreferences(
            touchToolConfig = ToolConfig.Pan,
            mouseToolConfig = ToolConfig.Select,
            stylusToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = true,
            enableClipboardWatching = false,
        )

        lateinit var inlineEditPaneState: InlineEditPaneState

        composeUiTest.setContent {
            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            val preferences = loadedPreferencesState.value

            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = composeLifePreferences,
                preferences = preferences,
                cellStateParser = cellStateParserProvider.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        assertEquals(
            ToolConfig.Pan,
            inlineEditPaneState.touchToolConfig,
        )
        assertEquals(
            ToolConfig.Draw,
            inlineEditPaneState.stylusToolConfig,
        )
        assertEquals(
            ToolConfig.Select,
            inlineEditPaneState.mouseToolConfig,
        )

        val clipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingDisabled>(clipboardWatchingState)
    }
}

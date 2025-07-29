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
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.globalGraph
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

@ContributesTo(AppScope::class)
interface InlineEditPaneStateTestsEntryPoint {
    val testComposeLifePreferences: TestComposeLifePreferences
    val cellStateParser: CellStateParser
}

// TODO: Replace with asContribution()
val ApplicationGraph.inlineEditPaneStateTestsEntryPoint: InlineEditPaneStateTestsEntryPoint get() =
    this as InlineEditPaneStateTestsEntryPoint

@OptIn(ExperimentalTestApi::class)
class InlineEditPaneStateTests : BaseUiInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
) {
    private val entryPoint get() = applicationGraph.inlineEditPaneStateTestsEntryPoint

    private val testComposeLifePreferences get() = entryPoint.testComposeLifePreferences

    @Test
    fun initial_state_is_correct_when_onboarding() = runUiTest {
        testComposeLifePreferences.touchToolConfig = ToolConfig.Pan
        testComposeLifePreferences.mouseToolConfig = ToolConfig.Select
        testComposeLifePreferences.stylusToolConfig = ToolConfig.Draw
        testComposeLifePreferences.completedClipboardWatchingOnboarding = false
        testComposeLifePreferences.enableClipboardWatching = true

        lateinit var inlineEditPaneState: InlineEditPaneState

        setContent {
            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = testComposeLifePreferences,
                preferences = testComposeLifePreferences.preferences,
                cellStateParser = entryPoint.cellStateParser,
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
    fun allowing_clipboard_watching_updates_state_correctly() = runUiTest {
        testComposeLifePreferences.touchToolConfig = ToolConfig.Pan
        testComposeLifePreferences.mouseToolConfig = ToolConfig.Select
        testComposeLifePreferences.stylusToolConfig = ToolConfig.Draw
        testComposeLifePreferences.completedClipboardWatchingOnboarding = false
        testComposeLifePreferences.enableClipboardWatching = true

        lateinit var inlineEditPaneState: InlineEditPaneState

        setContent {
            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = testComposeLifePreferences,
                preferences = testComposeLifePreferences.preferences,
                cellStateParser = entryPoint.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        val initialClipboardWatchingState = inlineEditPaneState.clipboardWatchingState
        assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

        initialClipboardWatchingState.onAllowClipboardWatching()

        waitForIdle()

        val newPreferences = testComposeLifePreferences.preferences

        assertTrue(newPreferences.completedClipboardWatchingOnboarding)
        assertTrue(newPreferences.enableClipboardWatching)

        val newClipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingEnabled>(newClipboardWatchingState)
    }

    @Test
    fun disallowing_clipboard_watching_updates_state_correctly() = runUiTest {
        testComposeLifePreferences.touchToolConfig = ToolConfig.Pan
        testComposeLifePreferences.mouseToolConfig = ToolConfig.Select
        testComposeLifePreferences.stylusToolConfig = ToolConfig.Draw
        testComposeLifePreferences.completedClipboardWatchingOnboarding = false
        testComposeLifePreferences.enableClipboardWatching = true

        lateinit var inlineEditPaneState: InlineEditPaneState

        setContent {
            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = testComposeLifePreferences,
                preferences = testComposeLifePreferences.preferences,
                cellStateParser = entryPoint.cellStateParser,
                setSelectionToCellState = {},
                onViewDeserializationInfo = {},
            )
        }

        val initialClipboardWatchingState = inlineEditPaneState.clipboardWatchingState
        assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

        initialClipboardWatchingState.onDisallowClipboardWatching()

        waitForIdle()

        val newPreferences = testComposeLifePreferences.preferences

        assertTrue(newPreferences.completedClipboardWatchingOnboarding)
        assertFalse(newPreferences.enableClipboardWatching)

        val newClipboardWatchingState = inlineEditPaneState.clipboardWatchingState

        assertIs<ClipboardWatchingState.ClipboardWatchingDisabled>(newClipboardWatchingState)
    }

    @Test
    fun initial_state_is_correct_when_clipboard_watching_enabled() = runUiTest {
        testComposeLifePreferences.touchToolConfig = ToolConfig.Pan
        testComposeLifePreferences.mouseToolConfig = ToolConfig.Select
        testComposeLifePreferences.stylusToolConfig = ToolConfig.Draw
        testComposeLifePreferences.completedClipboardWatchingOnboarding = true
        testComposeLifePreferences.enableClipboardWatching = true

        lateinit var inlineEditPaneState: InlineEditPaneState

        setContent {
            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = testComposeLifePreferences,
                preferences = testComposeLifePreferences.preferences,
                cellStateParser = entryPoint.cellStateParser,
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
    fun initial_state_is_correct_when_clipboard_watching_disabled() = runUiTest {
        testComposeLifePreferences.touchToolConfig = ToolConfig.Pan
        testComposeLifePreferences.mouseToolConfig = ToolConfig.Select
        testComposeLifePreferences.stylusToolConfig = ToolConfig.Draw
        testComposeLifePreferences.completedClipboardWatchingOnboarding = true
        testComposeLifePreferences.enableClipboardWatching = false

        lateinit var inlineEditPaneState: InlineEditPaneState

        setContent {
            inlineEditPaneState = rememberInlineEditPaneState(
                composeLifePreferences = testComposeLifePreferences,
                preferences = testComposeLifePreferences.preferences,
                cellStateParser = entryPoint.cellStateParser,
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

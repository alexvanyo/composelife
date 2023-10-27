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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.longClick
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.cells.SelectionState
import com.alexvanyo.composelife.ui.app.resources.ClearSelection
import com.alexvanyo.composelife.ui.app.resources.Collapse
import com.alexvanyo.composelife.ui.app.resources.Copy
import com.alexvanyo.composelife.ui.app.resources.Cut
import com.alexvanyo.composelife.ui.app.resources.DisableAutofit
import com.alexvanyo.composelife.ui.app.resources.EnableAutofit
import com.alexvanyo.composelife.ui.app.resources.Expand
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pause
import com.alexvanyo.composelife.ui.app.resources.Play
import com.alexvanyo.composelife.ui.app.resources.Step
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.util.isAndroid
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ActionControlRowTests {

    @Test
    fun no_selection_false_values_are_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Play))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Play)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Step))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Step)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Paste))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Paste)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.EnableAutofit))
            .assertIsDisplayed()
            .assertIsOff()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.EnableAutofit)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Expand))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Expand)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }
    }

    @Test
    fun no_selection_true_values_are_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = true,
                setIsRunning = {},
                onStep = {},
                isExpanded = true,
                setIsExpanded = {},
                isViewportTracking = true,
                setIsViewportTracking = {},
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Pause))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Pause)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Step))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Step)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.ClearSelection))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.Copy))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.Cut))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.Paste))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Paste)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.DisableAutofit))
            .assertIsDisplayed()
            .assertIsOn()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.DisableAutofit)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Collapse))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Collapse)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }
    }

    @Test
    fun selecting_box_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
                selectionState = SelectionState.SelectingBox(
                    topLeft = IntOffset.Zero,
                    width = 1,
                    height = 1,
                ),
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Play))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.Step))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.ClearSelection))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.ClearSelection)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Copy))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Copy)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Cut))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Cut)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Paste))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Paste)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.EnableAutofit))
            .assertIsDisplayed()
            .assertIsOff()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.EnableAutofit)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }

        onNodeWithContentDescription(resolver(Strings.Expand))
            .assertIsDisplayed()
            .assertHasClickAction()
            .performTouchInput {
                longClick()
            }

        if (isAndroid()) {
            onNode(hasText(resolver(Strings.Expand)) and hasAnyAncestor(isPopup()))
                .assertIsDisplayed()
        }
    }

    @Test
    fun on_step_updates_correctly() = runComposeUiTest {
        var onStepCount = 0
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = { onStepCount++ },
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Step))
            .performClick()

        assertEquals(1, onStepCount)
    }

    @Test
    fun play_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Play))
            .performClick()

        assertTrue(isRunning)
    }

    @Test
    fun pause_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(true)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Pause))
            .performClick()

        assertFalse(isRunning)
    }

    @Test
    fun expand_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Expand))
            .performClick()

        assertTrue(isExpanded)
    }

    @Test
    fun collapse_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(true)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Collapse))
            .performClick()

        assertFalse(isExpanded)
    }

    @Test
    fun enable_autofit_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.EnableAutofit))
            .performClick()

        assertTrue(isViewportTracking)
    }

    @Test
    fun disable_autofit_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.NoSelection,
                onClearSelection = {},
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.DisableAutofit))
            .performClick()

        assertFalse(isViewportTracking)
    }

    @Test
    fun on_clear_selection_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)
        var onClearSelectionCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.SelectingBox(
                    topLeft = IntOffset.Zero,
                    width = 1,
                    height = 1,
                ),
                onClearSelection = { onClearSelectionCount++ },
                onCopy = {},
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.ClearSelection))
            .performClick()

        assertEquals(1, onClearSelectionCount)
    }

    @Test
    fun on_copy_selection_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)
        var onCopyCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.SelectingBox(
                    topLeft = IntOffset.Zero,
                    width = 1,
                    height = 1,
                ),
                onClearSelection = {},
                onCopy = { onCopyCount++ },
                onCut = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.Copy))
            .performClick()

        assertEquals(1, onCopyCount)
    }

    @Test
    fun on_cut_selection_updates_correctly() = runComposeUiTest {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)
        var onCutCount = 0

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
                selectionState = SelectionState.SelectingBox(
                    topLeft = IntOffset.Zero,
                    width = 1,
                    height = 1,
                ),
                onClearSelection = {},
                onCopy = {},
                onCut = { onCutCount++ },
            )
        }

        onNodeWithContentDescription(resolver(Strings.Cut))
            .performClick()

        assertEquals(1, onCutCount)
    }
}

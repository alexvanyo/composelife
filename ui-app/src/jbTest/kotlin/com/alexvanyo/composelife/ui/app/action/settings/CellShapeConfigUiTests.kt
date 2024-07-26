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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsNotFocused
import androidx.compose.ui.test.assertTextContains
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.text.input.ImeAction
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabel
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.CornerFractionValue
import com.alexvanyo.composelife.ui.app.resources.RoundRectangle
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabel
import com.alexvanyo.composelife.ui.app.resources.SizeFractionLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.SizeFractionValue
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class CellShapeConfigUiTests {

    @Test
    fun round_rectangle_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        val composeLifePreferences = TestComposeLifePreferences(
            roundRectangleConfig = CurrentShape.RoundRectangle(0.8f, 0.4f),
        )
        val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        val preferences = loadedPreferencesState.value

        setContent {
            resolver = parameterizedStringResolver()

            val cellShapeConfigUiState = with(
                object : LoadedComposeLifePreferencesProvider, ComposeLifePreferencesProvider {
                    override val composeLifePreferences = composeLifePreferences
                    override val preferences = preferences
                },
            ) {
                rememberCellShapeConfigUiState()
            }

            CellShapeConfigUi(cellShapeConfigUiState = cellShapeConfigUiState)
        }

        onNodeWithText(resolver(Strings.RoundRectangle))
            .assertExists()
            .assertHasClickAction()

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.SizeFractionLabel)),
        )
            .assertTextContains(resolver(Strings.SizeFractionValue(0.8f)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.SizeFractionLabelAndValue(0.8f)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.CornerFractionLabel)),
        )
            .assertTextContains(resolver(Strings.CornerFractionValue(0.4f)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.CornerFractionLabelAndValue(0.4f)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_size_fraction_slider_updates_state() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        val composeLifePreferences = TestComposeLifePreferences(
            roundRectangleConfig = CurrentShape.RoundRectangle(0.8f, 0.4f),
        )
        val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        val preferences = loadedPreferencesState.value

        setContent {
            resolver = parameterizedStringResolver()

            val cellShapeConfigUiState = with(
                object : LoadedComposeLifePreferencesProvider, ComposeLifePreferencesProvider {
                    override val composeLifePreferences = composeLifePreferences
                    override val preferences = preferences
                },
            ) {
                rememberCellShapeConfigUiState()
            }

            CellShapeConfigUi(cellShapeConfigUiState = cellShapeConfigUiState)
        }

        onNodeWithContentDescription(
            resolver(Strings.SizeFractionLabelAndValue(0.8f)),
        )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        onNodeWithContentDescription(
            resolver(Strings.SizeFractionLabelAndValue(0.5f)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0.1f..1f)))
    }

    @Test
    fun round_rectangle_corner_fraction_slider_updates_state() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        val composeLifePreferences = TestComposeLifePreferences(
            roundRectangleConfig = CurrentShape.RoundRectangle(0.8f, 0.4f),
        )
        val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        val preferences = loadedPreferencesState.value

        setContent {
            resolver = parameterizedStringResolver()

            val cellShapeConfigUiState = with(
                object : LoadedComposeLifePreferencesProvider, ComposeLifePreferencesProvider {
                    override val composeLifePreferences = composeLifePreferences
                    override val preferences = preferences
                },
            ) {
                rememberCellShapeConfigUiState()
            }

            CellShapeConfigUi(cellShapeConfigUiState = cellShapeConfigUiState)
        }

        onNodeWithContentDescription(
            resolver(Strings.CornerFractionLabelAndValue(0.4f)),
        )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0f)
            }

        onNodeWithContentDescription(
            resolver(Strings.CornerFractionLabelAndValue(0f)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_popup_displays_options() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        val composeLifePreferences = TestComposeLifePreferences(
            roundRectangleConfig = CurrentShape.RoundRectangle(0.8f, 0.4f),
        )
        val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        val preferences = loadedPreferencesState.value

        setContent {
            resolver = parameterizedStringResolver()

            val cellShapeConfigUiState = with(
                object : LoadedComposeLifePreferencesProvider, ComposeLifePreferencesProvider {
                    override val composeLifePreferences = composeLifePreferences
                    override val preferences = preferences
                },
            ) {
                rememberCellShapeConfigUiState()
            }

            CellShapeConfigUi(cellShapeConfigUiState = cellShapeConfigUiState)
        }

        onNodeWithText(resolver(Strings.RoundRectangle))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(resolver(Strings.RoundRectangle)))
            .assertHasClickAction()
            .performClick()

        assertEquals(CurrentShapeType.RoundRectangle, composeLifePreferences.currentShapeType)

        onNode(isPopup())
            .assertDoesNotExist()
    }
}

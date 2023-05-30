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

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
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
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.text.input.ImeAction
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.ui.app.R
import kotlinx.coroutines.test.runTest
import leakcanary.SkipLeakDetection
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class CellShapeConfigUiTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun round_rectangle_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            CellShapeConfigUi(
                currentShape = CurrentShape.RoundRectangle(
                    sizeFraction = 0.8f,
                    cornerFraction = 0.4f,
                ),
                setCurrentShapeType = {},
                setRoundRectangleConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.round_rectangle))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(context.getString(R.string.size_fraction_label)),
            )
            .assertTextContains(context.getString(R.string.size_fraction_value, 0.8f))
            .assertIsNotFocused()
        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction_label_and_value, 0.8f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        composeTestRule
            .onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(context.getString(R.string.corner_fraction_label)),
            )
            .assertTextContains(context.getString(R.string.corner_fraction_value, 0.4f))
            .assertIsNotFocused()
        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction_label_and_value, 0.4f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_size_fraction_slider_updates_state() = runTest {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            CellShapeConfigUi(
                currentShape = roundRectangleShape,
                setCurrentShapeType = {},
                setRoundRectangleConfig = {
                    val result = it(roundRectangleShape)
                    sizeFraction = result.sizeFraction
                    cornerFraction = result.cornerFraction
                },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction_label_and_value, 0.8f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction_label_and_value, 0.5f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0.1f..1f)))
    }

    @Test
    fun round_rectangle_corner_fraction_slider_updates_state() = runTest {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            CellShapeConfigUi(
                currentShape = roundRectangleShape,
                setCurrentShapeType = {},
                setRoundRectangleConfig = {
                    val result = it(roundRectangleShape)
                    sizeFraction = result.sizeFraction
                    cornerFraction = result.cornerFraction
                },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction_label_and_value, 0.4f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction_label_and_value, 0f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..0.5f)))
    }

    @SkipLeakDetection("https://issuetracker.google.com/issues/206177594", "Inner")
    @Test
    fun round_rectangle_popup_displays_options() = runTest {
        var setCurrentShapeType: CurrentShapeType? = null

        composeTestRule.setContent {
            CellShapeConfigUi(
                currentShape = CurrentShape.RoundRectangle(
                    sizeFraction = 0.8f,
                    cornerFraction = 0.4f,
                ),
                setCurrentShapeType = {
                    setCurrentShapeType = it
                },
                setRoundRectangleConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.round_rectangle))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.round_rectangle)))
            .assertHasClickAction()
            .performClick()

        assertEquals(CurrentShapeType.RoundRectangle, setCurrentShapeType)

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()
    }
}

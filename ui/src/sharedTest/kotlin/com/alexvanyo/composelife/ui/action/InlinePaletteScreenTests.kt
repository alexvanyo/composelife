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

package com.alexvanyo.composelife.ui.action

import android.app.Application
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performSemanticsAction
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class InlinePaletteScreenTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val applicationContext = ApplicationProvider.getApplicationContext<Application>()

    @Test
    fun loading_is_displayed_correctly() {
        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = ResourceState.Loading,
                setCurrentShapeType = {},
                setRoundRectangleConfig = {},
            )
        }

        composeTestRule
            .onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }

    @Test
    fun round_rectangle_is_displayed_correctly() {
        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = ResourceState.Success(
                    CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.4f,
                    ),
                ),
                setCurrentShapeType = {},
                setRoundRectangleConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(applicationContext.getString(R.string.round_rectangle))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.size_fraction, 0.8f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.corner_fraction, 0.4f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_is_displayed_correctly_after_updating() {
        var currentShapeState by mutableStateOf<ResourceState<CurrentShape>>(ResourceState.Loading)

        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = currentShapeState,
                setCurrentShapeType = {},
                setRoundRectangleConfig = {},
            )
        }

        currentShapeState = ResourceState.Success(
            CurrentShape.RoundRectangle(
                sizeFraction = 0.8f,
                cornerFraction = 0.4f,
            ),
        )

        composeTestRule
            .onNodeWithText(applicationContext.getString(R.string.round_rectangle))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.size_fraction, 0.8f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.corner_fraction, 0.4f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_size_fraction_slider_updates_state() {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = ResourceState.Success(roundRectangleShape),
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
                applicationContext.getString(R.string.size_fraction, 0.8f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.size_fraction, 0.5f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0.1f..1f)))
    }

    @Test
    fun round_rectangle_corner_fraction_slider_updates_state() {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = ResourceState.Success(roundRectangleShape),
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
                applicationContext.getString(R.string.corner_fraction, 0.4f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.corner_fraction, 0f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..0.5f)))
    }
}

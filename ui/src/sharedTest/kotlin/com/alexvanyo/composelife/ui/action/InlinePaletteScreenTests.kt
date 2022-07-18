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
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performSemanticsAction
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.test.BaseHiltTest
import com.alexvanyo.composelife.test.TestActivity
import com.alexvanyo.composelife.ui.R
import dagger.hilt.EntryPoints
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import leakcanary.SkipLeakDetection
import org.junit.Before
import org.junit.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class InlinePaletteScreenTests : BaseHiltTest<TestActivity>(TestActivity::class.java) {

    lateinit var inlinePaletteScreenEntryPoint: InlinePaletteScreenEntryPoint

    @Before
    fun setup() {
        inlinePaletteScreenEntryPoint =
            EntryPoints.get(composeTestRule.activity, InlinePaletteScreenEntryPoint::class.java)
    }

    @Test
    fun loading_is_displayed_correctly() = runAppTest {
        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
                InlinePaletteScreen(
                    currentShapeState = ResourceState.Loading,
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }

        composeTestRule
            .onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }

    @Test
    fun round_rectangle_is_displayed_correctly() = runAppTest {
        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
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
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.round_rectangle))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction, 0.8f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction, 0.4f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_is_displayed_correctly_after_updating() = runAppTest {
        var currentShapeState by mutableStateOf<ResourceState<CurrentShape>>(ResourceState.Loading)

        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
                InlinePaletteScreen(
                    currentShapeState = currentShapeState,
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }

        currentShapeState = ResourceState.Success(
            CurrentShape.RoundRectangle(
                sizeFraction = 0.8f,
                cornerFraction = 0.4f,
            ),
        )

        composeTestRule
            .onNodeWithText(context.getString(R.string.round_rectangle))
            .assertExists()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction, 0.8f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.8f, range = 0.1f..1f)))

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction, 0.4f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.4f, range = 0f..0.5f)))
    }

    @Test
    fun round_rectangle_size_fraction_slider_updates_state() = runAppTest {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
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
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction, 0.8f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.size_fraction, 0.5f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0.1f..1f)))
    }

    @Test
    fun round_rectangle_corner_fraction_slider_updates_state() = runAppTest {
        var sizeFraction by mutableStateOf(0.8f)
        var cornerFraction by mutableStateOf(0.4f)

        val roundRectangleShape by derivedStateOf {
            CurrentShape.RoundRectangle(
                sizeFraction = sizeFraction,
                cornerFraction = cornerFraction,
            )
        }

        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
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
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction, 0.4f),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.corner_fraction, 0f),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..0.5f)))
    }

    @SkipLeakDetection("https://issuetracker.google.com/issues/206177594", "Inner")
    @Test
    fun round_rectangle_popup_displays_options() = runAppTest {
        var setCurrentShapeType: CurrentShapeType? = null

        composeTestRule.setContent {
            with(inlinePaletteScreenEntryPoint) {
                InlinePaletteScreen(
                    currentShapeState = ResourceState.Success(
                        CurrentShape.RoundRectangle(
                            sizeFraction = 0.8f,
                            cornerFraction = 0.4f,
                        ),
                    ),
                    setCurrentShapeType = {
                        setCurrentShapeType = it
                    },
                    setRoundRectangleConfig = {},
                )
            }
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

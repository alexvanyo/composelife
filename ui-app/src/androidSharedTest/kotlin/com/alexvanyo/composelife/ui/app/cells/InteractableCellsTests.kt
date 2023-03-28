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

package com.alexvanyo.composelife.ui.app.cells

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.dragAndDrop
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performMouseInput
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.DpOffset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.geometry.toPx
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.ui.app.R
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class InteractableCellsTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    private val interactableCellsLocalEntryPoint = object : InteractableCellsLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun cells_are_displayed_correctly() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
        )

        composeTestRule.setContent {
            with(interactableCellsLocalEntryPoint) {
                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    scaledCellDpSize = 10.dp,
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(8, 8),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 0),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 1),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 2),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 3),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 4),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 0),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 1),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 2),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 3),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 4),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 8, 8),
            )
            .assertExists()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, -1, -1),
            )
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 9, 9),
            )
            .assertDoesNotExist()
    }

    @Test
    fun clicking_on_cell_updates_state() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
        )

        composeTestRule.setContent {
            with(interactableCellsLocalEntryPoint) {
                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    scaledCellDpSize = 10.dp,
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(8, 8),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 4),
            )
            .assertIsOn()
            .performTouchInput { click(topLeft) }

        assertEquals(
            setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
            mutableGameOfLifeState.cellState,
        )
    }

    @OptIn(ExperimentalTestApi::class)
    @Test
    fun drawing_on_cells_with_mouse_updates_state() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
        )

        lateinit var density: Density

        composeTestRule.setContent {
            density = LocalDensity.current
            with(interactableCellsLocalEntryPoint) {
                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    scaledCellDpSize = 10.dp,
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(8, 8),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        composeTestRule
            .onNodeWithTag("CellCanvas")
            .performMouseInput {
                dragAndDrop(
                    with(density) { DpOffset(25.dp, 5.dp).toPx() },
                    with(density) { DpOffset(25.dp, 45.dp).toPx() },
                )
            }

        assertEquals(
            setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 1,
                2 to 2,
                2 to 3,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
            mutableGameOfLifeState.cellState,
        )
    }
}

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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.dragAndDrop
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performMouseInput
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.DpOffset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.geometry.toPx
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.ui.cells.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.cells.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InteractableCellsTests {

    private val interactableCellsLocalEntryPoint = object : InteractableCellsLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun cells_are_displayed_correctly() = runComposeUiTest {
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

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            with(interactableCellsLocalEntryPoint) {
                resolver = parameterizedStringResolver()

                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    setSelectionSessionState = {},
                    scaledCellDpSize = 50.dp,
                    cellWindow = CellWindow(
                        IntRect(
                            IntOffset(0, 0),
                            IntSize(9, 9),
                        ),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(0, 0)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(0, 1)),
        )
            .assertIsOff()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(0, 2)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(0, 3)),
        )
            .assertIsOff()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(0, 4)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 0)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 1)),
        )
            .assertIsOff()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 2)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 3)),
        )
            .assertIsOff()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 4)),
        )
            .assertIsOn()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(8, 8)),
        )
            .assertExists()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(-1, -1)),
        )
            .assertDoesNotExist()

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(9, 9)),
        )
            .assertDoesNotExist()
    }

    @Test
    fun clicking_on_cell_updates_state() = runComposeUiTest {
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

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            with(interactableCellsLocalEntryPoint) {
                resolver = parameterizedStringResolver()

                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    setSelectionSessionState = {},
                    scaledCellDpSize = 50.dp,
                    cellWindow = CellWindow(
                        IntRect(
                            IntOffset(0, 0),
                            IntSize(9, 9),
                        ),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        onNodeWithContentDescription(
            resolver(Strings.InteractableCellContentDescription(2, 4)),
        )
            .assertIsOn()
            .performClick()

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

    @Test
    fun drawing_on_cells_with_mouse_updates_state_with_draw_tool() = runComposeUiTest {
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

        setContent {
            density = LocalDensity.current
            with(
                object : InteractableCellsLocalEntryPoint {
                    override val preferences = LoadedComposeLifePreferences.Defaults.copy(
                        mouseToolConfig = ToolConfig.Draw,
                    )
                },
            ) {
                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    setSelectionSessionState = {},
                    scaledCellDpSize = 50.dp,
                    cellWindow = CellWindow(
                        IntRect(
                            IntOffset(0, 0),
                            IntSize(9, 9),
                        ),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        onNodeWithTag("CellCanvas")
            .performMouseInput {
                dragAndDrop(
                    with(density) { DpOffset(125.dp, 25.dp).toPx() },
                    with(density) { DpOffset(125.dp, 225.dp).toPx() },
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

    @Test
    fun drawing_on_cells_with_mouse_does_not_update_state_with_none_tool() = runComposeUiTest {
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

        setContent {
            density = LocalDensity.current
            with(
                object : InteractableCellsLocalEntryPoint {
                    override val preferences = LoadedComposeLifePreferences.Defaults.copy(
                        mouseToolConfig = ToolConfig.None,
                    )
                },
            ) {
                InteractableCells(
                    gameOfLifeState = mutableGameOfLifeState,
                    setSelectionSessionState = {},
                    scaledCellDpSize = 50.dp,
                    cellWindow = CellWindow(
                        IntRect(
                            IntOffset(0, 0),
                            IntSize(9, 9),
                        ),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }

        onNodeWithTag("CellCanvas")
            .performMouseInput {
                dragAndDrop(
                    with(density) { DpOffset(125.dp, 25.dp).toPx() },
                    with(density) { DpOffset(125.dp, 225.dp).toPx() },
                )
            }

        assertEquals(
            setOf(
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
            mutableGameOfLifeState.cellState,
        )
    }
}

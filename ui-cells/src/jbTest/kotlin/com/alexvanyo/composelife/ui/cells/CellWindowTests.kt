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

import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.ScrollWheel
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.test.performMouseInput
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.test.swipe
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.cells.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.cells.resources.Strings
import com.benasher44.uuid.uuid4
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class CellWindowTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {

    @Test
    fun cells_are_displayed_correctly() = runUiTest {
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by cellWindowInjectEntryPoint,
            CellWindowLocalEntryPoint by cellWindowLocalEntryPoint {}

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

        val selectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = uuid4(),
                valueId = uuid4(),
                value = SelectionState.NoSelection,
            ),
        )

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            with(entryPoint) {
                resolver = parameterizedStringResolver()

                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(50.dp),
                    cellWindowInteractionState = object :
                        MutableCellWindowInteractionState,
                        MutableSelectionStateHolder by selectionStateHolder {
                        override val viewportInteractionConfig: ViewportInteractionConfig
                            get() = ViewportInteractionConfig.Fixed(
                                CellWindowState(
                                    offset = Offset(-0.5f, -0.5f),
                                    scale = 1f,
                                ),
                            )
                    },
                    cellDpSize = 10.dp,
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
            resolver(Strings.InteractableCellContentDescription(0, 4)),
        )
            .assertDoesNotExist()

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
    }

    @Test
    fun cells_are_displayed_correctly_after_scrolling() = runUiTest {
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by cellWindowInjectEntryPoint,
            CellWindowLocalEntryPoint by cellWindowLocalEntryPoint {}

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

        val mutableCellWindowViewportState = MutableCellWindowViewportState()
        val selectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = uuid4(),
                valueId = uuid4(),
                value = SelectionState.NoSelection,
            ),
        )

        lateinit var density: Density

        setContent {
            density = LocalDensity.current

            with(
                object : CellWindowInjectEntryPoint by entryPoint, CellWindowLocalEntryPoint {
                    override val preferences = LoadedComposeLifePreferences.Defaults.copy(
                        touchToolConfig = ToolConfig.Pan,
                    )
                },
            ) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(150.dp),
                    cellWindowInteractionState = object :
                        MutableCellWindowInteractionState,
                        MutableSelectionStateHolder by selectionStateHolder {
                        override val viewportInteractionConfig: ViewportInteractionConfig
                            get() = ViewportInteractionConfig.Navigable(mutableCellWindowViewportState)
                    },
                    cellDpSize = 30.dp,
                )
            }
        }

        onRoot().performTouchInput {
            with(density) {
                swipe(
                    Offset(135.dp.toPx(), 135.dp.toPx()),
                    Offset(15.dp.toPx(), 15.dp.toPx()),
                )
            }
        }

        assertTrue(mutableCellWindowViewportState.offset.x > 3f)
        assertTrue(mutableCellWindowViewportState.offset.y > 3f)
    }

    @Test
    fun cells_are_not_scrolled_with_none_touch_tool_config() = runUiTest {
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by cellWindowInjectEntryPoint,
            CellWindowLocalEntryPoint by cellWindowLocalEntryPoint {}

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

        val mutableCellWindowViewportState = MutableCellWindowViewportState()
        val selectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = uuid4(),
                valueId = uuid4(),
                value = SelectionState.NoSelection,
            ),
        )

        lateinit var density: Density

        setContent {
            density = LocalDensity.current

            with(
                object : CellWindowInjectEntryPoint by entryPoint, CellWindowLocalEntryPoint {
                    override val preferences = LoadedComposeLifePreferences.Defaults.copy(
                        touchToolConfig = ToolConfig.None,
                    )
                },
            ) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(150.dp),
                    cellWindowInteractionState = object :
                        MutableCellWindowInteractionState,
                        MutableSelectionStateHolder by selectionStateHolder {
                        override val viewportInteractionConfig: ViewportInteractionConfig
                            get() = ViewportInteractionConfig.Navigable(mutableCellWindowViewportState)
                    },
                    cellDpSize = 30.dp,
                )
            }
        }

        onRoot().performTouchInput {
            with(density) {
                swipe(
                    Offset(135.dp.toPx(), 135.dp.toPx()),
                    Offset(15.dp.toPx(), 15.dp.toPx()),
                )
            }
        }

        assertEquals(
            Offset.Zero,
            mutableCellWindowViewportState.offset,
        )
    }

    @Test
    fun cells_are_displayed_correctly_after_zooming_in_with_mouse_wheel() = runUiTest {
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by cellWindowInjectEntryPoint,
            CellWindowLocalEntryPoint by cellWindowLocalEntryPoint {}

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

        val mutableCellWindowViewportState = MutableCellWindowViewportState()
        val selectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = uuid4(),
                valueId = uuid4(),
                value = SelectionState.NoSelection,
            ),
        )

        setContent {
            with(entryPoint) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(150.dp),
                    cellWindowInteractionState = object :
                        MutableCellWindowInteractionState,
                        MutableSelectionStateHolder by selectionStateHolder {
                        override val viewportInteractionConfig: ViewportInteractionConfig
                            get() = ViewportInteractionConfig.Navigable(mutableCellWindowViewportState)
                    },
                    cellDpSize = 30.dp,
                )
            }
        }

        onRoot().performMouseInput {
            scroll(-1f, ScrollWheel.Vertical)
        }

        assertEquals(10f / 9f, mutableCellWindowViewportState.scale)
    }

    @Test
    fun cells_are_displayed_correctly_after_zooming_out_with_mouse_wheel() = runUiTest {
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by cellWindowInjectEntryPoint,
            CellWindowLocalEntryPoint by cellWindowLocalEntryPoint {}

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

        val mutableCellWindowViewportState = MutableCellWindowViewportState()
        val selectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = uuid4(),
                valueId = uuid4(),
                value = SelectionState.NoSelection,
            ),
        )

        setContent {
            with(entryPoint) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(150.dp),
                    cellWindowInteractionState = object :
                        MutableCellWindowInteractionState,
                        MutableSelectionStateHolder by selectionStateHolder {
                        override val viewportInteractionConfig: ViewportInteractionConfig
                            get() = ViewportInteractionConfig.Navigable(mutableCellWindowViewportState)
                    },
                    cellDpSize = 30.dp,
                )
            }
        }

        onRoot().performMouseInput {
            scroll(1f, ScrollWheel.Vertical)
        }

        assertEquals(9f / 10f, mutableCellWindowViewportState.scale)
    }
}

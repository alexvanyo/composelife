/*
 * Copyright 2023 The Android Open Source Project
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
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.dragAndDrop
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performMouseInput
import androidx.compose.ui.unit.DpOffset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.geometry.toPx
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.cells.resources.SelectingBoxHandle
import com.alexvanyo.composelife.ui.cells.resources.Strings
import com.alexvanyo.composelife.ui.cells.util.isAndroid
import dev.zacsweers.metro.asContribution
import org.junit.Assume.assumeTrue
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
class SelectionOverlayTests : BaseUiInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
) {

    @Test
    fun no_selection_is_displayed_correctly() = runUiTest { uiGraph ->
        val injectEntryPoint = uiGraph.testComposeLifeUiEntryPoint
        val localEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by injectEntryPoint,
            CellWindowLocalEntryPoint by localEntryPoint {}

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()

            with(entryPoint) {
                SelectionOverlay(
                    selectionSessionState = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = SelectionState.NoSelection,
                    ),
                    setSelectionSessionState = {},
                    getSelectionCellState = { emptyCellState() },
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
            resolver(Strings.SelectingBoxHandle(0, 0)).substringBefore(":"),
        )
            .assertDoesNotExist()
    }

    @Test
    fun selecting_box_is_displayed_correctly() = runUiTest { uiGraph ->
        val injectEntryPoint = uiGraph.testComposeLifeUiEntryPoint
        val localEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by injectEntryPoint,
            CellWindowLocalEntryPoint by localEntryPoint {}

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()

            with(entryPoint) {
                SelectionOverlay(
                    selectionSessionState = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = SelectionState.SelectingBox.FixedSelectingBox(
                            topLeft = IntOffset(1, 1),
                            width = 2,
                            height = 3,
                            previousTransientSelectingBox = null,
                        ),
                    ),
                    setSelectionSessionState = {},
                    getSelectionCellState = { emptyCellState() },
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
            resolver(Strings.SelectingBoxHandle(1, 1)),
        )
            .assertIsDisplayed()

        onNodeWithContentDescription(
            resolver(Strings.SelectingBoxHandle(3, 1)),
        )
            .assertIsDisplayed()

        onNodeWithContentDescription(
            resolver(Strings.SelectingBoxHandle(1, 4)),
        )
            .assertIsDisplayed()

        onNodeWithContentDescription(
            resolver(Strings.SelectingBoxHandle(3, 4)),
        )
            .assertIsDisplayed()
    }

    @Test
    fun dragging_selecting_box_is_displayed_correctly() = runUiTest { uiGraph ->
        // TODO: This test tends to deadlock on desktop
        assumeTrue(isAndroid())

        val injectEntryPoint = uiGraph.testComposeLifeUiEntryPoint
        val localEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by injectEntryPoint,
            CellWindowLocalEntryPoint by localEntryPoint {}

        lateinit var resolver: (ParameterizedString) -> String

        val mutableSelectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = Uuid.random(),
                valueId = Uuid.random(),
                value = SelectionState.SelectingBox.FixedSelectingBox(
                    topLeft = IntOffset(2, 2),
                    width = 2,
                    height = 3,
                    previousTransientSelectingBox = null,
                ),
            ),
        )

        setContent {
            resolver = parameterizedStringResolver()

            with(entryPoint) {
                SelectionOverlay(
                    selectionSessionState = mutableSelectionStateHolder.selectionSessionState,
                    setSelectionSessionState = { mutableSelectionStateHolder.selectionSessionState = it },
                    getSelectionCellState = { emptyCellState() },
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
            resolver(Strings.SelectingBoxHandle(2, 2)),
        )
            .performMouseInput {
                val start = center
                val end = center + with(density) { DpOffset(200.dp, 200.dp).toPx() }
                dragAndDrop(start, end, durationMillis = 1_000)
            }

        assertEquals(
            SelectionState.SelectingBox.FixedSelectingBox(
                topLeft = IntOffset(4, 5),
                width = 2,
                height = 1,
                previousTransientSelectingBox = null,
            ),
            mutableSelectionStateHolder.selectionSessionState.value,
        )
    }

    @Test
    fun selection_is_displayed_correctly() = runUiTest { uiGraph ->
        val injectEntryPoint = uiGraph.testComposeLifeUiEntryPoint
        val localEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by injectEntryPoint,
            CellWindowLocalEntryPoint by localEntryPoint {}

        setContent {
            with(entryPoint) {
                SelectionOverlay(
                    selectionSessionState = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = SelectionState.Selection(
                            cellState = """
                                |.O.
                                |..O
                                |OOO
                            """.toCellState(),
                            offset = IntOffset(1, 1),
                        ),
                    ),
                    setSelectionSessionState = {},
                    getSelectionCellState = { emptyCellState() },
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

        onNodeWithTag("SelectionBox").assertIsDisplayed()
    }

    @Test
    fun dragging_selection_is_displayed_correctly() = runUiTest { uiGraph ->
        // TODO: This test tends to deadlock on desktop
        assumeTrue(isAndroid())

        val injectEntryPoint = uiGraph.testComposeLifeUiEntryPoint
        val localEntryPoint = object : CellWindowLocalEntryPoint {
            override val preferences = LoadedComposeLifePreferences.Defaults
        }

        val entryPoint = object :
            CellWindowInjectEntryPoint by injectEntryPoint,
            CellWindowLocalEntryPoint by localEntryPoint {}

        val mutableSelectionStateHolder = MutableSelectionStateHolder(
            SessionValue(
                sessionId = Uuid.random(),
                valueId = Uuid.random(),
                value = SelectionState.Selection(
                    cellState = """
                        |.O.
                        |..O
                        |OOO
                    """.trimIndent().toCellState(),
                    offset = IntOffset(1, 1),
                ),
            ),
        )

        setContent {
            with(entryPoint) {
                SelectionOverlay(
                    selectionSessionState = mutableSelectionStateHolder.selectionSessionState,
                    setSelectionSessionState = { mutableSelectionStateHolder.selectionSessionState = it },
                    getSelectionCellState = { emptyCellState() },
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

        onNodeWithTag("SelectionBox")
            .performMouseInput {
                val start = center
                val end = center + with(density) { DpOffset(200.dp, 200.dp).toPx() }
                dragAndDrop(start, end, durationMillis = 1_000)
            }

        assertEquals(
            SelectionState.Selection(
                cellState = """
                    |.O.
                    |..O
                    |OOO
                """.toCellState(),
                offset = IntOffset(5, 5),
            ),
            mutableSelectionStateHolder.selectionSessionState.value,
        )
    }
}

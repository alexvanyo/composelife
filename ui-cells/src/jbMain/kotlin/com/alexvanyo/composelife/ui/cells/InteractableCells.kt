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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.cells

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.SnapshotStateMap
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.geometry.isSpecified
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.HistoricalChange
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.geometry.LineSegmentPath
import com.alexvanyo.composelife.geometry.cellIntersections
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.currentShape
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.cells.resources.Strings
import com.alexvanyo.composelife.ui.util.detectDragGestures
import dev.zacsweers.metro.Inject
import kotlin.coroutines.cancellation.CancellationException
import kotlin.math.roundToInt
import kotlin.uuid.Uuid

// region templated-ctx
@Immutable
@Inject
class InteractableCellsCtx(
    private val preferencesHolder: LoadedComposeLifePreferencesHolder,
) {
    @Suppress("ComposableNaming", "LongParameterList")
    @Deprecated(
        "Ctx should not be invoked directly, instead use the top-level function",
        replaceWith = ReplaceWith(
            "InteractableCells(gameOfLifeState, setSelectionSessionState, scaledCellDpSize, cellWindow, " +
                "pixelOffsetFromCenter, modifier)",
        ),
    )
    @Composable
    operator fun invoke(
        gameOfLifeState: MutableGameOfLifeState,
        setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
        scaledCellDpSize: Dp,
        cellWindow: CellWindow,
        pixelOffsetFromCenter: Offset,
        modifier: Modifier = Modifier,
    ) = lambda(
        preferencesHolder,
        gameOfLifeState,
        setSelectionSessionState,
        scaledCellDpSize,
        cellWindow,
        pixelOffsetFromCenter,
        modifier,
    )

    companion object {
        private val lambda:
            @Composable
            context(
                LoadedComposeLifePreferencesHolder,
            ) (
                gameOfLifeState: MutableGameOfLifeState,
                setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
                scaledCellDpSize: Dp,
                cellWindow: CellWindow,
                pixelOffsetFromCenter: Offset,
                modifier: Modifier,
            ) -> Unit =
            {
                    gameOfLifeState,
                    setSelectionSessionState,
                    scaledCellDpSize,
                    cellWindow,
                    pixelOffsetFromCenter,
                    modifier,
                ->
                InteractableCells(
                    gameOfLifeState = gameOfLifeState,
                    setSelectionSessionState = setSelectionSessionState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                    pixelOffsetFromCenter = pixelOffsetFromCenter,
                    modifier = modifier,
                )
            }
    }
}

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
context(ctx: InteractableCellsCtx)
@Composable
@Suppress("LongParameterList", "DEPRECATION")
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) = ctx(gameOfLifeState, setSelectionSessionState, scaledCellDpSize, cellWindow, pixelOffsetFromCenter, modifier)
// endregion templated-ctx

context(preferencesHolder: LoadedComposeLifePreferencesHolder)
@Suppress("LongParameterList", "LongMethod")
@Composable
private fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier
            .graphicsLayer {
                this.translationX = -pixelOffsetFromCenter.x
                this.translationY = -pixelOffsetFromCenter.y
            }
            .requiredSize(
                scaledCellDpSize * cellWindow.width,
                scaledCellDpSize * cellWindow.height,
            ),
    ) {
        val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

        val numColumns = cellWindow.width
        val numRows = cellWindow.height

        val pendingCellChanges = remember { mutableStateMapOf<IntOffset, Boolean>() }

        val preferences = preferencesHolder.preferences
        val drawingPointerTypes =
            setOfNotNull(
                PointerType.Touch.takeIf { preferences.touchToolConfig == ToolConfig.Draw },
                PointerType.Stylus.takeIf { preferences.stylusToolConfig == ToolConfig.Draw },
                PointerType.Mouse.takeIf { preferences.mouseToolConfig == ToolConfig.Draw },
            )
        val erasingPointerTypes =
            setOfNotNull(
                PointerType.Touch.takeIf { preferences.touchToolConfig == ToolConfig.Erase },
                PointerType.Stylus.takeIf { preferences.stylusToolConfig == ToolConfig.Erase },
                PointerType.Mouse.takeIf { preferences.mouseToolConfig == ToolConfig.Erase },
            )
        val selectingPointerTypes =
            setOfNotNull(
                PointerType.Touch.takeIf { preferences.touchToolConfig == ToolConfig.Select },
                PointerType.Stylus.takeIf { preferences.stylusToolConfig == ToolConfig.Select },
                PointerType.Mouse.takeIf { preferences.mouseToolConfig == ToolConfig.Select },
            )

        Box(
            Modifier
                .requiredSize(
                    scaledCellDpSize * numColumns,
                    scaledCellDpSize * numRows,
                )
                .testTag("CellCanvas")
                .drawingCellInput(
                    drawingPointerTypes = drawingPointerTypes,
                    erasingPointerTypes = erasingPointerTypes,
                    gameOfLifeState = gameOfLifeState,
                    pendingCellChanges = pendingCellChanges,
                    scaledCellPixelSize = scaledCellPixelSize,
                    cellWindow = cellWindow,
                )
                .selectingCellInput(
                    selectingPointerTypes = selectingPointerTypes,
                    setSelectionSessionState = { setSelectionSessionState(it) },
                    scaledCellPixelSize = scaledCellPixelSize,
                    cellWindow = cellWindow,
                ),
        ) {
            Layout(
                modifier = Modifier.fillMaxSize(),
                content = {
                    cellWindow.containedPoints().forEach { cell ->
                        key(cell) {
                            val isAliveInState = cell in gameOfLifeState.cellState.aliveCells
                            InteractableCell(
                                modifier = Modifier
                                    .size(scaledCellDpSize),
                                drawState = when (pendingCellChanges[cell]) {
                                    false -> if (isAliveInState) DrawState.PendingDead else DrawState.Dead
                                    true -> if (isAliveInState) DrawState.Alive else DrawState.PendingAlive
                                    null -> if (isAliveInState) DrawState.Alive else DrawState.Dead
                                },
                                shape = preferences.currentShape,
                                contentDescription = parameterizedStringResource(
                                    Strings.InteractableCellContentDescription(
                                        x = cell.x,
                                        y = cell.y,
                                    ),
                                ),
                                onValueChange = { isAlive ->
                                    gameOfLifeState.setCellState(
                                        cellCoordinate = cell,
                                        isAlive = isAlive,
                                    )
                                },
                                onLongClick = {
                                    setSelectionSessionState(
                                        SessionValue(
                                            sessionId = Uuid.random(),
                                            valueId = Uuid.random(),
                                            value = SelectionState.SelectingBox.FixedSelectingBox(
                                                topLeft = cell,
                                                width = 1,
                                                height = 1,
                                                previousTransientSelectingBox = null,
                                            ),
                                        ),
                                    )
                                },
                            )
                        }
                    }
                },
                measurePolicy = { measurables, _ ->
                    val placeables = measurables.map { it.measure(Constraints()) }

                    layout(
                        (numColumns * scaledCellPixelSize).roundToInt(),
                        (numRows * scaledCellPixelSize).roundToInt(),
                    ) {
                        placeables.forEachIndexed { index, placeable ->
                            val rowIndex = index / numColumns
                            val columnIndex = index % numColumns
                            placeable.place(
                                (columnIndex * scaledCellPixelSize).roundToInt(),
                                (rowIndex * scaledCellPixelSize).roundToInt(),
                            )
                        }
                    }
                },
            )
        }
    }
}

@Suppress("LongParameterList", "ComposeComposableModifier", "ComposeModifierWithoutDefault")
@OptIn(ExperimentalComposeUiApi::class)
@Composable
private fun Modifier.drawingCellInput(
    drawingPointerTypes: Set<PointerType>,
    erasingPointerTypes: Set<PointerType>,
    gameOfLifeState: MutableGameOfLifeState,
    pendingCellChanges: SnapshotStateMap<IntOffset, Boolean>,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
): Modifier {
    val currentScaledCellPixelSize by rememberUpdatedState(scaledCellPixelSize)
    val currentCellWindow by rememberUpdatedState(cellWindow)

    return pointerInput(drawingPointerTypes, erasingPointerTypes, pendingCellChanges, gameOfLifeState) {
        detectDragGestures(
            excludedPointerTypes = setOf(PointerType.Touch, PointerType.Mouse, PointerType.Stylus) -
                drawingPointerTypes - erasingPointerTypes,
            onDragStart = {
                pendingCellChanges.clear()
            },
            onDragEnd = {
                if (pendingCellChanges.size == 1) {
                    // If the drawing change only hit one cell, treat it as a toggle
                    val cellCoordinate = pendingCellChanges.keys.first()
                    gameOfLifeState.setCellState(
                        cellCoordinate,
                        cellCoordinate !in gameOfLifeState.cellState.aliveCells,
                    )
                } else {
                    // Otherwise, add all of them
                    pendingCellChanges.forEach { (cellCoordinate, isAlive) ->
                        gameOfLifeState.setCellState(
                            cellCoordinate = cellCoordinate,
                            isAlive = isAlive,
                        )
                    }
                }
                pendingCellChanges.clear()
            },
            onDrag = { change, _ ->
                val path = LineSegmentPath(
                    (
                        listOf(change.previousPosition) +
                            change.historical.map(HistoricalChange::position) +
                            listOf(change.position)
                        )
                        .filter(Offset::isSpecified)
                        .map { it / currentScaledCellPixelSize },
                )
                val isAlive = when (change.type) {
                    in drawingPointerTypes -> true
                    in erasingPointerTypes -> false
                    else -> throw CancellationException("Non-drawing type!")
                }
                path.cellIntersections().forEach { localCoordinate ->
                    pendingCellChanges[localCoordinate + currentCellWindow.topLeft] = isAlive
                }
            },
        )
    }
}

@Suppress("LongMethod", "ComposeComposableModifier", "ComposeModifierWithoutDefault")
@Composable
private fun Modifier.selectingCellInput(
    selectingPointerTypes: Set<PointerType>,
    setSelectionSessionState: (SessionValue<SelectionState>) -> Unit,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
): Modifier {
    var isSelecting by remember { mutableStateOf(false) }
    var start by remember { mutableStateOf(Offset.Zero) }
    var end by remember { mutableStateOf(Offset.Zero) }
    val currentScaledCellPixelSize by rememberUpdatedState(scaledCellPixelSize)
    val currentCellWindow by rememberUpdatedState(cellWindow)
    val currentSetSelectionSessionState by rememberUpdatedState(setSelectionSessionState)

    var editingSessionId by remember { mutableStateOf(Uuid.random()) }

    DisposableEffect(Unit) {
        onDispose {
            if (isSelecting) {
                currentSetSelectionSessionState(
                    SessionValue(
                        sessionId = editingSessionId,
                        valueId = Uuid.random(),
                        value = SelectionState.NoSelection,
                    ),
                )
            }
        }
    }

    return pointerInput(selectingPointerTypes) {
        detectDragGestures(
            excludedPointerTypes = setOf(PointerType.Touch, PointerType.Mouse, PointerType.Stylus) -
                selectingPointerTypes,
            onDragStart = {
                isSelecting = true
                editingSessionId = Uuid.random()
                start = ((it / currentScaledCellPixelSize).round() + currentCellWindow.topLeft).toOffset()
                end = it / currentScaledCellPixelSize + currentCellWindow.topLeft.toOffset()
                currentSetSelectionSessionState(
                    SessionValue(
                        sessionId = editingSessionId,
                        valueId = Uuid.random(),
                        value = SelectionState.SelectingBox.TransientSelectingBox(
                            rect = Rect(topLeft = start, bottomRight = end),
                        ),
                    ),
                )
            },
            onDragEnd = {
                isSelecting = false
                currentSetSelectionSessionState(
                    SessionValue(
                        sessionId = editingSessionId,
                        valueId = Uuid.random(),
                        value = SelectionState.SelectingBox.FixedSelectingBox(
                            topLeft = start.round(),
                            width = (end.x - start.x).roundToInt(),
                            height = (end.y - start.y).roundToInt(),
                            previousTransientSelectingBox = SelectionState.SelectingBox.TransientSelectingBox(
                                rect = Rect(topLeft = start, bottomRight = end),
                            ),
                        ),
                    ),
                )
            },
            onDragCancel = {
                isSelecting = false
                currentSetSelectionSessionState(
                    SessionValue(
                        sessionId = editingSessionId,
                        valueId = Uuid.random(),
                        value = SelectionState.NoSelection,
                    ),
                )
            },
            onDrag = { change, _ ->
                end = change.position / currentScaledCellPixelSize + currentCellWindow.topLeft.toOffset()

                currentSetSelectionSessionState(
                    SessionValue(
                        sessionId = editingSessionId,
                        valueId = Uuid.random(),
                        value = SelectionState.SelectingBox.TransientSelectingBox(
                            rect = Rect(topLeft = start, bottomRight = end),
                        ),
                    ),
                )
            },
        )
    }
}

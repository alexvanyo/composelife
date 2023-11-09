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

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.foundation.gestures.detectDragGestures
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.isSpecified
import androidx.compose.ui.input.pointer.HistoricalChange
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.geometry.LineSegmentPath
import com.alexvanyo.composelife.geometry.cellIntersections
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import kotlin.coroutines.cancellation.CancellationException
import kotlin.math.roundToInt

interface InteractableCellsLocalEntryPoint : LoadedComposeLifePreferencesProvider

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
context(InteractableCellsLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    setSelectionState: (SelectionState) -> Unit,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier
            .requiredSize(
                scaledCellDpSize * cellWindow.width,
                scaledCellDpSize * cellWindow.height,
            ),
    ) {
        val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

        val numColumns = cellWindow.width
        val numRows = cellWindow.height

        val pendingCellChanges = remember { mutableStateMapOf<IntOffset, Boolean>() }

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
                                    setSelectionState(
                                        SelectionState.SelectingBox(
                                            topLeft = cell,
                                            width = 1,
                                            height = 1,
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

@Suppress("LongParameterList")
@OptIn(ExperimentalComposeUiApi::class)
private fun Modifier.drawingCellInput(
    drawingPointerTypes: Set<PointerType>,
    erasingPointerTypes: Set<PointerType>,
    gameOfLifeState: MutableGameOfLifeState,
    pendingCellChanges: MutableMap<IntOffset, Boolean>,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
): Modifier = composed {
    val currentScaledCellPixelSize by rememberUpdatedState(scaledCellPixelSize)
    val currentCellWindow by rememberUpdatedState(cellWindow)

    pointerInput(drawingPointerTypes, erasingPointerTypes, pendingCellChanges, gameOfLifeState) {
        detectDragGestures(
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
                    else -> throw CancellationException("Non-stylus type!")
                }
                path.cellIntersections().forEach { localCoordinate ->
                    pendingCellChanges[localCoordinate + currentCellWindow.topLeft] = isAlive
                }
            },
        )
    }
}

fun <T> AnchoredDraggable2DState<T>.isDraggingOrAnimating(): Boolean =
    anchors.positionOf(currentValue) != requireOffset()

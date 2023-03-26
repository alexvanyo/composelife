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
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.HistoricalChange
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.geometry.LineSegmentPath
import com.alexvanyo.composelife.geometry.cellIntersections
import com.alexvanyo.composelife.geometry.containedPoints
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlin.coroutines.cancellation.CancellationException
import kotlin.math.roundToInt

interface InteractableCellsLocalEntryPoint : LoadedComposeLifePreferencesProvider

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
context(InteractableCellsLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod", "CyclomaticComplexMethod")
@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
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
                scaledCellDpSize * (cellWindow.width + 1),
                scaledCellDpSize * (cellWindow.height + 1),
            ),
    ) {
        val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

        val numColumns = cellWindow.width + 1
        val numRows = cellWindow.height + 1

        val pendingCellChanges = remember { mutableStateMapOf<IntOffset, Boolean>() }

        Layout(
            modifier = Modifier
                .requiredSize(
                    scaledCellDpSize * numColumns,
                    scaledCellDpSize * numRows,
                )
                .testTag("CellCanvas")
                .drawingCellInput(
                    gameOfLifeState = gameOfLifeState,
                    pendingCellChanges = pendingCellChanges,
                    scaledCellPixelSize = scaledCellPixelSize,
                    cellWindow = cellWindow,
                ),
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
                            contentDescription = stringResource(
                                R.string.cell_content_description,
                                cell.x,
                                cell.y,
                            ),
                            onValueChange = { isAlive ->
                                gameOfLifeState.setCellState(
                                    cellCoordinate = cell,
                                    isAlive = isAlive,
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
                    placeables.mapIndexed { index, placeable ->
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

@OptIn(ExperimentalComposeUiApi::class)
private fun Modifier.drawingCellInput(
    gameOfLifeState: MutableGameOfLifeState,
    pendingCellChanges: MutableMap<IntOffset, Boolean>,
    scaledCellPixelSize: Float,
    cellWindow: IntRect,
): Modifier = composed {
    val currentScaledCellPixelSize by rememberUpdatedState(scaledCellPixelSize)
    val currentCellWindow by rememberUpdatedState(cellWindow)

    pointerInput(pendingCellChanges, gameOfLifeState) {
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
                    PointerType.Mouse, PointerType.Stylus -> true
                    PointerType.Eraser -> false
                    else -> throw CancellationException("Non-stylus type!")
                }
                path.cellIntersections().forEach { localCoordinate ->
                    pendingCellChanges[localCoordinate + currentCellWindow.topLeft] = isAlive
                }
            },
        )
    }
}

@ThemePreviews
@Composable
fun InteractableCellsPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Box(modifier = Modifier.size(300.dp)) {
                InteractableCells(
                    gameOfLifeState = MutableGameOfLifeState(
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
                    ),
                    scaledCellDpSize = 32.dp,
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(9, 9),
                    ),
                    pixelOffsetFromCenter = Offset.Zero,
                )
            }
        }
    }
}

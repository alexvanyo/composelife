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
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.alexvanyo.composelife.util.containedPoints
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

        Layout(
            modifier = modifier
                .requiredSize(
                    scaledCellDpSize * numColumns,
                    scaledCellDpSize * numRows,
                ),
            content = {
                cellWindow.containedPoints().forEach { cell ->
                    key(cell) {
                        InteractableCell(
                            modifier = Modifier
                                .size(scaledCellDpSize),
                            isAlive = cell in gameOfLifeState.cellState.aliveCells,
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

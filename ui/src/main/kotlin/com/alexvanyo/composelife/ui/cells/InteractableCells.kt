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

import android.content.res.Configuration
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.setCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    shape: CurrentShape,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier
            .requiredSize(
                scaledCellDpSize * (cellWindow.width + 1),
                scaledCellDpSize * (cellWindow.height + 1),
            ),
    ) {
        Column {
            (cellWindow.top..cellWindow.bottom).forEach { row ->
                Row {
                    (cellWindow.left..cellWindow.right).forEach { column ->
                        val cell = IntOffset(column, row)
                        key(cell) {
                            InteractableCell(
                                modifier = Modifier
                                    .size(scaledCellDpSize),
                                isAlive = cell in gameOfLifeState.cellState.aliveCells,
                                shape = shape,
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
                }
            }
        }
    }
}

@Preview(
    name = "Light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
    widthDp = 300,
    heightDp = 300,
)
@Preview(
    name = "Dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
    widthDp = 300,
    heightDp = 300,
)
@Composable
fun InteractableCellsPreview() {
    ComposeLifeTheme {
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
            shape = CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f,
            ),
            scaledCellDpSize = 32.dp,
            cellWindow = IntRect(
                IntOffset(0, 0),
                IntOffset(9, 9),
            ),
        )
    }
}

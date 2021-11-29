package com.alexvanyo.composelife.ui

import android.content.res.Configuration
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.data.model.GameOfLifeState
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.data.model.setIndividualCellState
import com.alexvanyo.composelife.data.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.util.containedPoints
import kotlin.math.roundToInt

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is interactable, so each cell is displayed by a unique [InteractableCell].
 */
@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    modifier: Modifier = Modifier
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
                        contentDescription = stringResource(
                            R.string.cell_content_description,
                            cell.x,
                            cell.y
                        ),
                        onValueChange = { isAlive ->
                            gameOfLifeState.setIndividualCellState(
                                cellCoordinate = cell,
                                isAlive = isAlive
                            )
                        }
                    )
                }
            }
        },
        measurePolicy = { measurables, constraints ->
            val placeables = measurables.map { it.measure(constraints) }

            layout(
                (numColumns * scaledCellPixelSize).roundToInt(),
                (numRows * scaledCellPixelSize).roundToInt(),
            ) {
                placeables.mapIndexed { index, placeable ->
                    val rowIndex = index / numColumns
                    val columnIndex = index % numColumns
                    placeable.place(
                        (columnIndex * scaledCellPixelSize).roundToInt(),
                        (rowIndex * scaledCellPixelSize).roundToInt()
                    )
                }
            }
        }
    )
}

@Preview(
    name = "Interactable cells light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
    widthDp = 300,
    heightDp = 300
)
@Preview(
    name = "Interactable cells dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
    widthDp = 300,
    heightDp = 300
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
                ).toCellState()
            ),
            scaledCellDpSize = 32.dp,
            cellWindow = IntRect(
                IntOffset(0, 0),
                IntOffset(9, 9)
            )
        )
    }
}

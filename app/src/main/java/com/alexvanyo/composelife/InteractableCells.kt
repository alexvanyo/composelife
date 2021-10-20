package com.alexvanyo.composelife

import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.dp
import kotlin.math.roundToInt

@Composable
fun InteractableCells(
    gameOfLifeState: MutableGameOfLifeState,
    scaledCellDpSize: Dp,
    numColumns: Int,
    numRows: Int,
    columnIndexOffset: Int,
    rowIndexOffset: Int,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    Layout(
        content = {
            repeat(numRows) { rowIndex ->
                repeat(numColumns) { columnIndex ->
                    val cellCoordinate = (columnIndex - columnIndexOffset) to (rowIndex - rowIndexOffset)

                    InteractableCell(
                        modifier = Modifier
                            .size(scaledCellDpSize),
                        isAlive = cellCoordinate in gameOfLifeState.cellState,
                        onClick = {
                            gameOfLifeState.setIndividualCellState(cellCoordinate, it)
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
                val centeringXPixelOffset = ((numColumns * scaledCellPixelSize) - constraints.maxWidth) / 2
                val centeringYPixelOffset = ((numRows * scaledCellPixelSize) - constraints.maxHeight) / 2

                placeables.mapIndexed { index, placeable ->
                    val rowIndex = index / numColumns
                    val columnIndex = index % numColumns
                    placeable.place(
                        (centeringXPixelOffset + columnIndex * scaledCellPixelSize).roundToInt(),
                        (centeringYPixelOffset + rowIndex * scaledCellPixelSize).roundToInt()
                    )
                }
            }
        }
    )
}

@Preview(
    widthDp = 300,
    heightDp = 300,
)
@Composable
fun InteractableCellsPreview() {
    InteractableCells(
        gameOfLifeState = MutableGameOfLifeStateImpl(
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
            ),
        ),
        scaledCellDpSize = 32.dp,
        numColumns = 10,
        numRows = 10,
        columnIndexOffset = 0,
        rowIndexOffset = 0
    )
}


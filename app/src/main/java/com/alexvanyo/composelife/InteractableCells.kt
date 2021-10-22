package com.alexvanyo.composelife

import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import kotlin.math.roundToInt

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
                InteractableCell(
                    modifier = Modifier
                        .size(scaledCellDpSize),
                    isAlive = cell in gameOfLifeState.cellState,
                    onClick = {
                        gameOfLifeState.setIndividualCellState(cell, it)
                    }
                )
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
    widthDp = 300,
    heightDp = 300,
)
@Composable
fun InteractableCellsPreview() {
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
            )
        ),
        scaledCellDpSize = 32.dp,
        cellWindow = IntRect(
            IntOffset(0, 0),
            IntOffset(9, 9)
        )
    )
}


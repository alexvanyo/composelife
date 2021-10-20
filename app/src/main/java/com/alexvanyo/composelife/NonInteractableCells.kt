package com.alexvanyo.composelife

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.dp

@Composable
fun NonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    numColumns: Int,
    numRows: Int,
    columnIndexOffset: Int,
    rowIndexOffset: Int,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    Canvas(
        modifier = Modifier
            .size(
                scaledCellDpSize * numColumns,
                scaledCellDpSize * numRows
            )
    ) {
        repeat(numRows) { rowIndex ->
            repeat(numColumns) { columnIndex ->
                val topLeft = Offset(columnIndex * scaledCellPixelSize, rowIndex * scaledCellPixelSize)
                val color =
                    if ((columnIndex - columnIndexOffset) to (rowIndex - rowIndexOffset) in gameOfLifeState.cellState) {
                        Color.White
                    } else {
                        Color.Black
                    }

                drawRect(
                    color = color,
                    topLeft = topLeft,
                    size = Size(scaledCellPixelSize, scaledCellPixelSize)
                )
            }
        }
    }
}

@Preview(
    widthDp = 300,
    heightDp = 300
)
@Composable
fun NonInteractableCellsPreview() {
    NonInteractableCells(
        gameOfLifeState = ImmutableGameOfLifeState(
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
        numColumns = 10,
        numRows = 10,
        columnIndexOffset = 0,
        rowIndexOffset = 0
    )
}

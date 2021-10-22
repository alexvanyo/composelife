package com.alexvanyo.composelife

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset

@Composable
fun NonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val numColumns = cellWindow.width + 1
    val numRows = cellWindow.height + 1

    Canvas(
        modifier = modifier
            .requiredSize(
                scaledCellDpSize * numColumns,
                scaledCellDpSize * numRows
            )
    ) {
        cellWindow.containedPoints().forEach { cell ->
            val windowOffset = (cell - cellWindow.topLeft).toOffset() * scaledCellPixelSize
            val color = if (cell in gameOfLifeState.cellState) {
                Color.White
            } else {
                Color.Black
            }

            drawRect(
                color = color,
                topLeft = windowOffset,
                size = Size(scaledCellPixelSize, scaledCellPixelSize)
            )
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
        gameOfLifeState = GameOfLifeState(
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

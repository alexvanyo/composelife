package com.alexvanyo.composelife.ui

import android.content.res.Configuration.UI_MODE_NIGHT_NO
import android.content.res.Configuration.UI_MODE_NIGHT_YES
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.material.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.data.model.GameOfLifeState
import com.alexvanyo.composelife.data.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.util.ExcludeFromJacocoGeneratedReport
import com.alexvanyo.composelife.util.containedPoints

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is not interactable, so for efficiency the cell window is represented
 * by a single [Canvas], where each cell is drawn individually.
 */
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

    val aliveColor = MaterialTheme.colors.onBackground
    val deadColor = MaterialTheme.colors.background

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
                aliveColor
            } else {
                deadColor
            }

            drawRect(
                color = color,
                topLeft = windowOffset,
                size = Size(scaledCellPixelSize, scaledCellPixelSize)
            )
        }
    }
}

@ExcludeFromJacocoGeneratedReport
private class NonInteractableCellsPreviews {

    @Preview(
        name = "Non interactable cells light mode",
        uiMode = UI_MODE_NIGHT_NO,
        widthDp = 300,
        heightDp = 300
    )
    @Preview(
        name = "Non interactable cells dark mode",
        uiMode = UI_MODE_NIGHT_YES,
        widthDp = 300,
        heightDp = 300
    )
    @Composable
    fun NonInteractableCellsPreview() {
        ComposeLifeTheme {
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
}

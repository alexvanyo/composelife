package com.alexvanyo.composelife.ui

import android.content.res.Configuration.UI_MODE_NIGHT_NO
import android.content.res.Configuration.UI_MODE_NIGHT_YES
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
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
    shape: CurrentShape,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    Canvas(
        modifier = modifier
            .requiredSize(
                scaledCellDpSize * (cellWindow.width + 1),
                scaledCellDpSize * (cellWindow.height + 1)
            )
    ) {
        drawRect(
            color = deadColor,
        )

        cellWindow.containedPoints().forEach { cell ->
            if (cell in gameOfLifeState.cellState.aliveCells) {
                when (shape) {
                    is CurrentShape.RoundRectangle -> {
                        drawRoundRect(
                            color = aliveColor,
                            topLeft = (cell - cellWindow.topLeft).toOffset() * scaledCellPixelSize +
                                Offset(
                                    scaledCellPixelSize * (1f - shape.sizeFraction) / 2f,
                                    scaledCellPixelSize * (1f - shape.sizeFraction) / 2f,
                                ),
                            size = Size(scaledCellPixelSize, scaledCellPixelSize) * shape.sizeFraction,
                            cornerRadius = CornerRadius(
                                scaledCellPixelSize * shape.sizeFraction * shape.cornerFraction
                            )
                        )
                    }
                }
            }
        }
    }
}

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
            shape = CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f
            ),
            cellWindow = IntRect(
                IntOffset(0, 0),
                IntOffset(9, 9)
            )
        )
    }
}

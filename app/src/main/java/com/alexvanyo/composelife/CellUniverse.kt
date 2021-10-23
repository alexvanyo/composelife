package com.alexvanyo.composelife

import android.util.Log
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.material.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import kotlin.math.ceil
import kotlin.math.floor

@Composable
fun CellUniverse(
    gameOfLifeState: MutableGameOfLifeState
) {
    var scale by remember { mutableStateOf(1f) }
    var offset by remember { mutableStateOf(Offset.Zero) }
    var isGesturing by remember { mutableStateOf(false) }

    BoxWithConstraints {
        val cellDpSize = 32.dp
        val scaledCellDpSize = cellDpSize * scale
        val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }
        val scaledCellPixelSize = cellPixelSize * scale

        val intOffset = IntOffset(floor(offset.x).toInt(), floor(offset.y).toInt())
        val fracOffset = offset - intOffset.toOffset()
        val fracPixelOffset = fracOffset * scaledCellPixelSize

        // Calculate the number of columns and rows necessary to cover the entire viewport.
        // Ensure that the number of rows and number of columns is odd, so that the offset is the center cell
        val numColumns = ceil(constraints.maxWidth / scaledCellPixelSize / 2).toInt() * 2 + 1
        val numRows = ceil(constraints.maxHeight / scaledCellPixelSize / 2).toInt() * 2 + 1

        val centeringIntOffset = IntOffset(-numColumns / 2, -numRows / 2)

        val cellWindow = IntRect(
            intOffset + centeringIntOffset,
            IntSize(
                numColumns,
                numRows
            )
        )

        val onGestureState = rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
            val oldScale = scale
            val newScale = (oldScale * zoom).coerceIn(0.1f, 3f)

            val centroidOffset = centroid / scaledCellPixelSize + centeringIntOffset.toOffset()

            val panDiff = pan / scaledCellPixelSize
            val zoomDiff = centroidOffset * (newScale / oldScale - 1)

            offset += zoomDiff - panDiff
            scale = newScale
        }

        Box(
            modifier = Modifier
                .graphicsLayer {
                    translationX = -fracPixelOffset.x
                    translationY = -fracPixelOffset.y
                }
                .pointerInput(Unit) {
                    detectTransformGestures(
                        onGestureStart = { isGesturing = true },
                        onGestureEnd = { isGesturing = false },
                        onGesture = { centroid: Offset, pan: Offset, zoom: Float, rotation: Float ->
                            onGestureState.value(centroid, pan, zoom, rotation)
                        }
                    )
                }
        ) {
            if (isGesturing || scale < 1f) {
                NonInteractableCells(
                    gameOfLifeState = gameOfLifeState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                )
            } else {
                InteractableCells(
                    gameOfLifeState = gameOfLifeState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                )
            }
        }
    }

    Text(
        text = "Offset: $offset",
        color = Color.White,
    )
}

@Preview(
    widthDp = 1000,
    heightDp = 1000,
)
@Composable
fun CellUniversePreview() {
    CellUniverse(
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
        )
    )
}

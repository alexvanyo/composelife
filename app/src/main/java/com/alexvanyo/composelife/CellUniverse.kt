package com.alexvanyo.composelife

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import kotlin.math.ceil

@Composable
fun CellUniverse(
    gameOfLifeState: MutableGameOfLifeState
) {
    var scale by remember { mutableStateOf(1f) }
    var offset by remember { mutableStateOf(Offset.Zero) }
    var isGesturing by remember { mutableStateOf(false) }

    val cellDpSize = 32.dp
    val scaledCellDpSize = cellDpSize * scale
    val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }
    val scaledCellPixelSize = cellPixelSize * scale

    val columnIndexOffset = ceil(offset.x).toInt()
    val rowIndexOffset = ceil(offset.y).toInt()

    val columnPixelOffset = (offset.x - columnIndexOffset) * scaledCellPixelSize
    val rowPixelOffset = (offset.y - rowIndexOffset) * scaledCellPixelSize

    val onGestureState = rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
        val oldOffset = offset
        val oldScale = scale
        val newScale = (oldScale * zoom).coerceIn(0.1f, 3f)

        val centroidPosition =
            oldOffset + pan / (cellPixelSize * oldScale) - centroid / (cellPixelSize * oldScale)
        offset = centroidPosition + centroid / (cellPixelSize * newScale)
        scale = newScale
    }

    BoxWithConstraints(
        modifier = Modifier
            .graphicsLayer {
                translationX = columnPixelOffset
                translationY = rowPixelOffset
            }
            .pointerInput(Unit) {
                detectTransformGestures(
                    onGestureStart = { isGesturing = true },
                    onGestureEnd = { isGesturing = false },
                    onGesture = onGestureState.value
                )
            }
    ) {
        val numColumns = ceil(constraints.maxWidth / scaledCellPixelSize).toInt() + 1
        val numRows = ceil(constraints.maxHeight / scaledCellPixelSize).toInt() + 1

        if (isGesturing || scale < 1f) {
            NonInteractableCells(
                gameOfLifeState = gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                numColumns = numColumns,
                numRows = numRows,
                columnIndexOffset = columnIndexOffset,
                rowIndexOffset = rowIndexOffset,
            )
        } else {
            InteractableCells(
                gameOfLifeState = gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                numColumns = numColumns,
                numRows = numRows,
                columnIndexOffset = columnIndexOffset,
                rowIndexOffset = rowIndexOffset,
            )
        }
    }
}

@Preview(
    widthDp = 1000,
    heightDp = 1000,
)
@Composable
fun CellUniversePreview() {
    CellUniverse(
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
            )
        )
    )
}

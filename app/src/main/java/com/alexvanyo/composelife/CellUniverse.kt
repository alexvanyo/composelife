package com.alexvanyo.composelife

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.offset
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.setValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import kotlin.math.ceil
import kotlin.math.roundToInt

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
        val newScale = (oldScale * zoom).coerceIn(0.1f, 2f)

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
            val centeringXPixelOffset = ((numColumns * scaledCellPixelSize) - constraints.maxWidth) / 2
            val centeringYPixelOffset = ((numRows * scaledCellPixelSize) - constraints.maxHeight) / 2

            val centeringXDpOffset = with(LocalDensity.current) { centeringXPixelOffset.toDp() }
            val centeringYDpOffset = with(LocalDensity.current) { centeringYPixelOffset.toDp() }

            Layout(
                modifier = Modifier.offset(x = centeringXDpOffset, y = centeringYDpOffset),
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

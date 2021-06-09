package com.alexvanyo.composelife

import androidx.compose.foundation.gestures.detectDragGestures
import androidx.compose.foundation.gestures.detectTransformGestures
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.offset
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.setValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlin.math.ceil
import kotlin.math.roundToInt

@Composable
fun CellUniverse(
    cellState: Set<Pair<Int, Int>>
) {
    var scale by remember { mutableStateOf(1f) }
    var offset by remember { mutableStateOf(Offset.Zero) }
    var isGesturing by remember { mutableStateOf(false) }

    val cellDpSize = 32.dp * scale
    val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }

    val columnIndexOffset = ceil(offset.x / cellPixelSize).toInt()
    val rowIndexOffset = ceil(offset.y / cellPixelSize).toInt()

    val columnPixelOffset = offset.x - (columnIndexOffset * cellPixelSize)
    val rowPixelOffset = offset.y - (rowIndexOffset * cellPixelSize)

    BoxWithConstraints(
        modifier = Modifier
            .graphicsLayer {
                translationX = columnPixelOffset
                translationY = rowPixelOffset
            }
            .pointerInput(Unit) {
                coroutineScope {
                    launch {
                        detectTransformGestures { _, pan, zoom, _ ->
                            offset += pan
                            scale *= zoom
                            scale = scale.coerceIn(0.1f, 2f)
                        }
                    }
                    launch {
                        detectDragGestures(
                            onDragStart = {
                                isGesturing = true
                            },
                            onDragEnd = {
                                isGesturing = false
                            }
                        ) { _, dragAmount ->
                            offset += dragAmount
                        }
                    }
                }
            },
    ) {

        val numColumns = ceil(constraints.maxWidth / cellPixelSize).toInt() + 1
        val numRows = ceil(constraints.maxHeight / cellPixelSize).toInt() + 1

        if (isGesturing || cellDpSize < 32.dp) {
            NonInteractableCells(
                cellState = cellState,
                cellDpSize = cellDpSize,
                numColumns = numColumns,
                numRows = numRows,
                columnIndexOffset = columnIndexOffset,
                rowIndexOffset = rowIndexOffset,
            )
        } else {
            val centeringXPixelOffset = ((numColumns * cellPixelSize) - constraints.maxWidth) / 2
            val centeringYPixelOffset = ((numRows * cellPixelSize) - constraints.maxHeight) / 2

            val centeringXDpOffset = with(LocalDensity.current) { centeringXPixelOffset.toDp() }
            val centeringYDpOffset = with(LocalDensity.current) { centeringYPixelOffset.toDp() }

            Layout(
                modifier = Modifier.offset(x = centeringXDpOffset, y = centeringYDpOffset),
                content = {
                    repeat(numRows) { rowIndex ->
                        repeat(numColumns) { columnIndex ->
                            InteractableCell(
                                modifier = Modifier
                                    .size(cellDpSize),
                                isAlive = (columnIndex - columnIndexOffset) to (rowIndex - rowIndexOffset) in cellState,
                                onClick = {}
                            )
                        }
                    }
                },
                measurePolicy = { measurables, constraints ->
                    val placeables = measurables.map { it.measure(constraints) }

                    layout(
                        (numColumns * cellPixelSize).roundToInt(),
                        (numRows * cellPixelSize).roundToInt(),
                    ) {
                        placeables.mapIndexed { index, placeable ->
                            val rowIndex = index / numColumns
                            val columnIndex = index % numColumns
                            placeable.place(
                                (columnIndex * cellPixelSize).roundToInt(),
                                (rowIndex * cellPixelSize).roundToInt()
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
        cellState = setOf(
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
}

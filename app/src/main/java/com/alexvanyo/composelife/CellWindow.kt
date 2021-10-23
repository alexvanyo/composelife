package com.alexvanyo.composelife

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.runtime.Composable
import androidx.compose.runtime.MutableState
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import kotlin.math.ceil
import kotlin.math.floor

@Composable
fun rememberCellWindowState(
    offset: Offset = CellWindowState.defaultOffset,
    scale: Float = CellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = CellWindowState.defaultScaleRange
): CellWindowState =
    rememberSaveable(saver = CellWindowStateImpl.Saver) {
        CellWindowStateImpl(
            offset = offset,
            scale = scale,
            scaleRange = scaleRange
        )
    }

/**
 * A state holder describing a specific window into the cell universe.
 */
@Stable
interface CellWindowState {

    /**
     * The [Offset] (in cell coordinates) of the center focused cell.
     *
     * Positive x is to the right, and positive y is to the bottom.
     */
    var offset: Offset

    /**
     * The scale of the current cell window. This is a multiplicative scale, so `1` is the default scale,
     * `2` corresponds to cells twice as big, and `0.5` corresponds to cells half as big.
     */
    var scale: Float

    /**
     * The allowed range that [scale] can take. This cannot be an empty range.
     */
    var scaleRange: ClosedRange<Float>

    companion object {
        val defaultOffset = Offset.Zero
        const val defaultScale = 1f
        val defaultScaleRange = 0.1f..3f
    }
}

fun CellWindowState(
    offset: Offset = CellWindowState.defaultOffset,
    scale: Float = CellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = CellWindowState.defaultScaleRange
): CellWindowState = CellWindowStateImpl(
    offset = offset,
    scale = scale,
    scaleRange = scaleRange
)

private class CellWindowStateImpl(
    offset: Offset = Offset.Zero,
    scale: Float = 1f,
    scaleRange: ClosedRange<Float> = 0.1f..3f
) : CellWindowState {
    override var offset: Offset by mutableStateOf(offset)

    private var _scaleRange: MutableState<ClosedRange<Float>> = mutableStateOf(scaleRange)

    override var scaleRange: ClosedRange<Float>
        get() = _scaleRange.value
        set(value) {
            require(!scaleRange.isEmpty())  { "scaleRange cannot be empty" }
            _scaleRange.value = value
            // Set scale, to coerce the value to the new range (if necessary)
            scale = scale
        }

    private var _scale: MutableState<Float> = mutableStateOf(scale)

    override var scale: Float
        get() = _scale.value
        set(value) {
            _scale.value = value.coerceIn(scaleRange)
        }

    init {
        // Ensure invariants are met
        this.scaleRange = scaleRange
        this.scale = scale
    }

    companion object {
        val Saver: Saver<CellWindowState, *> = listSaver(
            { listOf(it.offset.x, it.offset.y, it.scale, it.scaleRange.start, it.scaleRange.endInclusive) },
            {
                CellWindowStateImpl(
                    offset = Offset(it[0], it[1]),
                    scale = it[2],
                    scaleRange = it[3]..it[4]
                )
            }
        )
    }
}

@Composable
fun CellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    cellWindowState: CellWindowState = rememberCellWindowState(),
    cellDpSize: Dp = 32.dp
) {
    var isGesturing by remember { mutableStateOf(false) }

    val scaledCellDpSize = cellDpSize * cellWindowState.scale

    val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }
    val scaledCellPixelSize = cellPixelSize * cellWindowState.scale

    BoxWithConstraints {
        val intOffset = IntOffset(floor(cellWindowState.offset.x).toInt(), floor(cellWindowState.offset.y).toInt())
        val fracOffset = cellWindowState.offset - intOffset.toOffset()
        val fracPixelOffset = fracOffset * scaledCellPixelSize

        // Calculate the number of columns and rows necessary to cover the entire viewport.
        // Ensure that the number of rows and number of columns is odd, so that the offset is the center cell
        val numColumns = ceil(constraints.maxWidth / scaledCellPixelSize).toInt().ceilToOdd()
        val numRows = ceil(constraints.maxHeight / scaledCellPixelSize).toInt().ceilToOdd()

        val centeringIntOffset = IntOffset(-numColumns / 2, -numRows / 2)

        val cellWindow = IntRect(
            intOffset + centeringIntOffset,
            IntSize(
                numColumns,
                numRows
            )
        )

        val onGestureState = rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
            val oldScale = cellWindowState.scale
            cellWindowState.scale = oldScale * zoom

            val centroidOffset = centroid / scaledCellPixelSize + centeringIntOffset.toOffset()

            val panDiff = pan / scaledCellPixelSize
            val zoomDiff = centroidOffset * (cellWindowState.scale / oldScale - 1)

            cellWindowState.offset += zoomDiff - panDiff
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
            if (isGesturing || scaledCellDpSize < 32.dp) {
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
}

package com.alexvanyo.composelife.ui

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
import com.alexvanyo.composelife.data.model.GameOfLifeState
import com.alexvanyo.composelife.data.model.MutableGameOfLifeState
import com.alexvanyo.composelife.util.ceilToOdd
import com.alexvanyo.composelife.ui.util.detectTransformGestures
import com.alexvanyo.composelife.util.floor
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.math.ceil

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

private sealed interface CellWindowUiState {

    val gameOfLifeState: GameOfLifeState

    class ImmutableState(
        override val gameOfLifeState: GameOfLifeState
    ) : CellWindowUiState

    class MutableState(
        override val gameOfLifeState: MutableGameOfLifeState,
        val isInteractable: (isGesturing: Boolean, scaledCellDpSize: Dp) -> Boolean
    ) : CellWindowUiState
}

/**
 * A cell window that displays the given [gameOfLifeState] in an immutable fashion.
 */
@Composable
fun ImmutableCellWindow(
    gameOfLifeState: GameOfLifeState,
    cellWindowState: CellWindowState = rememberCellWindowState(),
    cellDpSize: Dp = 32.dp,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.ImmutableState(
            gameOfLifeState = gameOfLifeState
        ),
        cellWindowState = cellWindowState,
        cellDpSize = cellDpSize
    )
}

/**
 * A cell window that displays the given [gameOfLifeState] in an mutable fashion.
 *
 * If [isInteractable] returns true, the
 */
@Composable
fun MutableCellWindow(
    gameOfLifeState: MutableGameOfLifeState,
    isInteractable: (isGesturing: Boolean, scaledCellDpSize: Dp) -> Boolean = { isGesturing, scaledCellDpSize ->
        !isGesturing && scaledCellDpSize >= 32.dp
    },
    cellWindowState: CellWindowState = rememberCellWindowState(),
    cellDpSize: Dp = 32.dp,
) {
    CellWindowImpl(
        cellWindowUiState = CellWindowUiState.MutableState(
            gameOfLifeState = gameOfLifeState,
            isInteractable = isInteractable
        ),
        cellWindowState = cellWindowState,
        cellDpSize = cellDpSize
    )
}

@Composable
private fun CellWindowImpl(
    cellWindowUiState: CellWindowUiState,
    cellWindowState: CellWindowState,
    cellDpSize: Dp,
) {
    var isGesturing by remember { mutableStateOf(false) }

    val scaledCellDpSize = cellDpSize * cellWindowState.scale

    val cellPixelSize = with(LocalDensity.current) { cellDpSize.toPx() }
    val scaledCellPixelSize = cellPixelSize * cellWindowState.scale

    BoxWithConstraints {
        // Convert the window state offset into integer and fractional parts
        val intOffset = floor(cellWindowState.offset)
        val fracOffset = cellWindowState.offset - intOffset.toOffset()
        val fracPixelOffset = fracOffset * scaledCellPixelSize

        // Calculate the number of columns and rows necessary to cover the entire viewport.
        // Ensure that the number of rows and number of columns is odd, so that the offset is the center cell
        val numColumns = ceil(constraints.maxWidth / scaledCellPixelSize).toInt().ceilToOdd()
        val numRows = ceil(constraints.maxHeight / scaledCellPixelSize).toInt().ceilToOdd()

        // Compute the offset from the main offset to the top left corner, in cell coordinates
        val topLeftOffset = IntOffset(-numColumns / 2, -numRows / 2)

        // Compute the cell window, describing all of the cells that will be drawn
        val cellWindow = IntRect(
            intOffset + topLeftOffset,
            IntSize(
                numColumns,
                numRows
            )
        )

        val onGestureState = rememberUpdatedState { centroid: Offset, pan: Offset, zoom: Float, _: Float ->
            val oldScale = cellWindowState.scale

            // Compute the offset from the centroid to the underlying offset, in cell coordinates
            val centroidOffset = centroid / scaledCellPixelSize + topLeftOffset.toOffset()

            // Compute the offset update due to panning
            val panDiff = pan / scaledCellPixelSize

            // Update the scale
            cellWindowState.scale = oldScale * zoom

            // Compute offset update due to zooming. We adjust the offset by the distance it moved relative to the
            // centroid, which allows the centroid to be the point that remains fixed while zooming.
            val zoomDiff = centroidOffset * (cellWindowState.scale / oldScale - 1)

            // Update the offset
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
            if (
                cellWindowUiState.isInteractable(
                    isGesturing = isGesturing,
                    scaledCellDpSize = scaledCellDpSize
                )
            ) {
                InteractableCells(
                    gameOfLifeState = cellWindowUiState.gameOfLifeState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                )
            } else {
                NonInteractableCells(
                    gameOfLifeState = cellWindowUiState.gameOfLifeState,
                    scaledCellDpSize = scaledCellDpSize,
                    cellWindow = cellWindow,
                )
            }
        }
    }
}

@OptIn(ExperimentalContracts::class)
private fun CellWindowUiState.isInteractable(
    isGesturing: Boolean,
    scaledCellDpSize: Dp,
): Boolean {
    contract { returns(true) implies (this@isInteractable is CellWindowUiState.MutableState) }
    return when (this) {
        is CellWindowUiState.ImmutableState -> false
        is CellWindowUiState.MutableState -> isInteractable(
            isGesturing,
            scaledCellDpSize
        )
    }
}

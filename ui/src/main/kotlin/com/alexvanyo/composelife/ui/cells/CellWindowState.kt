package com.alexvanyo.composelife.ui.cells

import androidx.compose.runtime.Composable
import androidx.compose.runtime.MutableState
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Offset

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

@Composable
fun rememberCellWindowState(
    offset: Offset = CellWindowState.defaultOffset,
    scale: Float = CellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = CellWindowState.defaultScaleRange,
): CellWindowState =
    rememberSaveable(saver = CellWindowStateImpl.Saver) {
        CellWindowState(
            offset = offset,
            scale = scale,
            scaleRange = scaleRange
        )
    }

fun CellWindowState(
    offset: Offset = CellWindowState.defaultOffset,
    scale: Float = CellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = CellWindowState.defaultScaleRange,
): CellWindowState = CellWindowStateImpl(
    offset = offset,
    scale = scale,
    scaleRange = scaleRange
)

private class CellWindowStateImpl(
    offset: Offset = Offset.Zero,
    scale: Float = 1f,
    scaleRange: ClosedRange<Float> = 0.1f..3f,
) : CellWindowState {
    override var offset: Offset by mutableStateOf(offset)

    private var _scaleRange: MutableState<ClosedRange<Float>> = mutableStateOf(scaleRange)

    override var scaleRange: ClosedRange<Float>
        get() = _scaleRange.value
        set(value) {
            require(!scaleRange.isEmpty()) { "scaleRange cannot be empty" }
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

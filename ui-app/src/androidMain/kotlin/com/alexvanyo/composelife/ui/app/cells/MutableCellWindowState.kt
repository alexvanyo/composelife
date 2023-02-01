/*
 * Copyright 2022 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Offset

/**
 * A state holder describing a specific viewport into the cell universe.
 */
@Stable
interface MutableCellWindowState : CellWindowState {

    /**
     * The [Offset] (in cell coordinates) of the center focused cell.
     *
     * Positive x is to the right, and positive y is to the bottom.
     */
    override var offset: Offset

    /**
     * The scale of the current cell window. This is a multiplicative scale, so `1` is the default scale,
     * `2` corresponds to cells twice as big, and `0.5` corresponds to cells half as big.
     */
    override var scale: Float

    /**
     * The allowed range that [scale] can take. This cannot be an empty range.
     */
    var scaleRange: ClosedRange<Float>

    companion object {
        val defaultOffset = Offset.Zero
        const val defaultScale = 1f
        val defaultScaleRange = 0.01f..3f
    }
}

/**
 * Remembers a [MutableCellWindowState], with the given default
 */
@Composable
fun rememberMutableCellWindowState(
    offset: Offset = MutableCellWindowState.defaultOffset,
    scale: Float = MutableCellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = MutableCellWindowState.defaultScaleRange,
): MutableCellWindowState =
    rememberSaveable(saver = MutableCellWindowStateImpl.Saver) {
        MutableCellWindowState(
            offset = offset,
            scale = scale,
            scaleRange = scaleRange,
        )
    }

fun MutableCellWindowState(
    offset: Offset = MutableCellWindowState.defaultOffset,
    scale: Float = MutableCellWindowState.defaultScale,
    scaleRange: ClosedRange<Float> = MutableCellWindowState.defaultScaleRange,
): MutableCellWindowState = MutableCellWindowStateImpl(
    offset = offset,
    scale = scale,
    scaleRange = scaleRange,
)

private class MutableCellWindowStateImpl(
    offset: Offset = Offset.Zero,
    scale: Float = 1f,
    scaleRange: ClosedRange<Float> = 0.1f..3f,
) : MutableCellWindowState {
    override var offset: Offset by mutableStateOf(offset)

    private var _scaleRange by mutableStateOf(scaleRange)

    override var scaleRange: ClosedRange<Float>
        get() = _scaleRange
        set(value) {
            require(!scaleRange.isEmpty()) { "scaleRange cannot be empty" }
            _scaleRange = value
            // Set scale, to coerce the value to the new range (if necessary)
            scale = scale
        }

    private var _scale by mutableStateOf(scale)

    override var scale: Float
        get() = _scale
        set(value) {
            _scale = value.coerceIn(scaleRange)
        }

    init {
        // Ensure invariants are met
        this.scaleRange = scaleRange
        this.scale = scale
    }

    companion object {
        val Saver: Saver<MutableCellWindowState, *> = listSaver(
            { listOf(it.offset.x, it.offset.y, it.scale, it.scaleRange.start, it.scaleRange.endInclusive) },
            {
                MutableCellWindowStateImpl(
                    offset = Offset(it[0], it[1]),
                    scale = it[2],
                    scaleRange = it[3]..it[4],
                )
            },
        )
    }
}

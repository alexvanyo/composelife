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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Offset
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.serialization.ClosedFloatRangeSerializer
import com.alexvanyo.composelife.serialization.OffsetSerializer
import com.alexvanyo.composelife.serialization.SurrogatingSerializer
import com.alexvanyo.composelife.serialization.saver
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * A state holder describing a specific viewport into the cell universe.
 */
@Stable
interface MutableCellWindowViewportState : CellWindowViewportState {

    override var cellWindowViewport: CellWindowViewport

    /**
     * The [Offset] (in cell coordinates) of the center focused cell.
     *
     * Positive x is to the right, and positive y is to the bottom.
     */
    fun setOffset(offset: Offset)

    /**
     * The scale of the current cell window. This is a multiplicative scale, so `1` is the default scale,
     * `2` corresponds to cells twice as big, and `0.5` corresponds to cells half as big.
     */
    fun setScale(scale: Float)

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
 * Remembers a [MutableCellWindowViewportState], with the given default
 */
@Composable
fun rememberMutableCellWindowViewportState(
    offset: Offset = MutableCellWindowViewportState.defaultOffset,
    scale: Float = MutableCellWindowViewportState.defaultScale,
    scaleRange: ClosedRange<Float> = MutableCellWindowViewportState.defaultScaleRange,
): MutableCellWindowViewportState =
    rememberSaveable(saver = MutableCellWindowViewportStateImpl.Saver) {
        MutableCellWindowViewportStateImpl(
            offset = offset,
            scale = scale,
            scaleRange = scaleRange,
        )
    }

fun MutableCellWindowViewportState(
    offset: Offset = MutableCellWindowViewportState.defaultOffset,
    scale: Float = MutableCellWindowViewportState.defaultScale,
    scaleRange: ClosedRange<Float> = MutableCellWindowViewportState.defaultScaleRange,
): MutableCellWindowViewportState = MutableCellWindowViewportStateImpl(
    offset = offset,
    scale = scale,
    scaleRange = scaleRange,
)

@Serializable(with = MutableCellWindowViewportStateImpl.Serializer::class)
private class MutableCellWindowViewportStateImpl(
    offset: Offset = Offset.Zero,
    scale: Float = 1f,
    scaleRange: ClosedRange<Float> = 0.1f..3f,
) : MutableCellWindowViewportState {

    private constructor(surrogate: Surrogate) : this(
        surrogate.offset,
        surrogate.scale,
        surrogate.scaleRange,
    )

    private var _offset: Offset by mutableStateOf(offset)

    private var _scaleRange by mutableStateOf(scaleRange)

    override var scaleRange: ClosedRange<Float>
        get() = _scaleRange
        set(value) {
            require(!scaleRange.isEmpty()) { "scaleRange cannot be empty" }
            _scaleRange = value
            // Set scale, to coerce the value to the new range (if necessary)
            setScale(scale)
        }

    private var _scale by mutableFloatStateOf(scale)

    override var cellWindowViewport: CellWindowViewport
        get() = CellWindowViewport(_offset, _scale)
        set(value) {
            setOffset(value.offset)
            setScale(value.scale)
        }

    init {
        // Ensure invariants are met
        this.scaleRange = scaleRange
        setScale(scale)
    }

    override fun setOffset(offset: Offset) {
        _offset = offset
    }

    override fun setScale(scale: Float) {
        _scale = scale.coerceIn(scaleRange)
    }

    private val surrogate: Surrogate get() =
        Surrogate(
            offset = offset,
            scale = scale,
            scaleRange = scaleRange,
        )

    @Serializable
    @SerialName("MutableCellWindowViewportStateImpl")
    private data class Surrogate(
        @Serializable(with = OffsetSerializer::class)
        val offset: Offset,
        val scale: Float,
        @Serializable(with = ClosedFloatRangeSerializer::class)
        val scaleRange: ClosedRange<Float>,
    )

    private object Serializer : KSerializer<MutableCellWindowViewportStateImpl> by SurrogatingSerializer(
        MutableCellWindowViewportStateImpl::surrogate,
        ::MutableCellWindowViewportStateImpl,
    )

    companion object {
        val Saver: Saver<MutableCellWindowViewportStateImpl, SavedState> = serializer().saver()
    }
}

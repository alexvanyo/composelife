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

import androidx.compose.runtime.Stable
import androidx.compose.ui.geometry.Offset

/**
 * A state holder describing a specific viewport into the cell universe.
 */
@Stable
interface CellWindowViewportState {

    /**
     * Returns the [CellWindowViewport] corresponding to the given [CellWindowViewportState].
     */
    val cellWindowViewport: CellWindowViewport
}

/**
 * The [Offset] (in cell coordinates) of the center focused cell.
 *
 * Positive x is to the right, and positive y is to the bottom.
 */
val CellWindowViewportState.offset: Offset
    get() = cellWindowViewport.offset

/**
 * The scale of the current cell window. This is a multiplicative scale, so `1` is the default scale,
 * `2` corresponds to cells twice as big, and `0.5` corresponds to cells half as big.
 */
val CellWindowViewportState.scale: Float
    get() = cellWindowViewport.scale

fun CellWindowState(
    offset: Offset,
    scale: Float,
): CellWindowViewportState = CellWindowState(
    cellWindowViewport = CellWindowViewport(
        offset = offset,
        scale = scale,
    ),
)

fun CellWindowState(
    cellWindowViewport: CellWindowViewport,
): CellWindowViewportState = object : CellWindowViewportState {
    override val cellWindowViewport = cellWindowViewport
}

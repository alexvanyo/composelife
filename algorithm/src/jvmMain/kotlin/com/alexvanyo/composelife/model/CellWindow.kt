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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize

/**
 * A finite rectangular region of a cell universe.
 *
 * This is represented by an [IntRect], with the [IntRect.topLeft] being the top-left most point (inclusive), and
 * [IntRect.bottomRight] being the bottom-right most point (exclusive).
 */
@JvmInline
value class CellWindow(private val intRect: IntRect) {

    init {
        require(intRect.top <= intRect.bottom)
        require(intRect.left <= intRect.right)
    }

    val topLeft: IntOffset get() = intRect.topLeft

    val topRight: IntOffset get() = intRect.topRight

    val bottomRight: IntOffset get() = intRect.bottomRight

    val bottomLeft: IntOffset get() = intRect.bottomLeft

    val center: IntOffset get() = intRect.center

    val top: Int get() = intRect.top

    val left: Int get() = intRect.left

    val bottom: Int get() = intRect.bottom

    val right: Int get() = intRect.right

    val width: Int get() = intRect.width

    val height: Int get() = intRect.height

    val size: IntSize get() = intRect.size

    fun translate(intOffset: IntOffset): CellWindow =
        CellWindow(intRect.translate(intOffset))

    /**
     * Returns all [IntOffset]s that are contained in the [CellWindow].
     * The points are returned in row-major order.
     */
    fun containedPoints(): List<IntOffset> =
        (top until bottom).flatMap { row ->
            (left until right).map { column ->
                IntOffset(column, row)
            }
        }
}

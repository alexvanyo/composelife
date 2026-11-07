/*
 * Copyright 2024 The Android Open Source Project
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

/**
 * A serializer for a [CellStateFormat.FixedFormat].
 *
 * This can directly and synchronously deserialize a sequence of lines into a [DeserializationResult] with
 * [deserializeToCellState], and serialize a [CellState] into a sequence of lines with [serializeToString].
 */
interface FixedFormatCellStateSerializer {
    val format: CellStateFormat.FixedFormat

    fun deserializeToCellState(lines: Sequence<String>): DeserializationResult

    fun serializeToString(cellState: CellState): Sequence<String>
}

/**
 * The [Char] for a Unicode code point reported by a deserializer, or the replacement character if it doesn't fit in
 * a single [Char].
 */
internal fun codePointToChar(codePoint: UInt): Char = if (codePoint <= 0xFFFFu) codePoint.toInt().toChar() else '�'

/**
 * The cells as the keys the Lean serializers take (`cellBits`): the bits of the x coordinate in the high half, and of
 * the y coordinate in the low half.
 */
@OptIn(ExperimentalUnsignedTypes::class)
internal fun Collection<IntOffset>.toLeanCells(): ULongArray {
    val keys = ULongArray(size)
    forEachIndexed { index, cell ->
        keys[index] = (cell.x.toUInt().toULong() shl 32) or cell.y.toUInt().toULong()
    }
    return keys
}

/**
 * The cells whose keys a Lean deserializer returned (see [toLeanCells]).
 */
@OptIn(ExperimentalUnsignedTypes::class)
internal fun leanCellsToOffsets(keys: ULongArray): Set<IntOffset> {
    val cells = HashSet<IntOffset>(keys.size)
    for (key in keys) {
        cells.add(IntOffset((key shr 32).toUInt().toInt(), key.toUInt().toInt()))
    }
    return cells
}

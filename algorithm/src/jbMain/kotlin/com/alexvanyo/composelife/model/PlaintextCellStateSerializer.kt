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

object PlaintextCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Plaintext

    @Suppress("UNCHECKED_CAST")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val linesArray = lines.toList().toTypedArray()
        val result = f_Algorithm_deserializePlaintext(linesArray as Array<Any?>)

        val warnings = result.warnings.map {
            val w = it as PlaintextWarning
            when (w.tag) {
                0u -> UnexpectedBlankLineMessage(w.lineIndex.toInt())

                1u -> UnexpectedShortLineMessage(w.lineIndex.toInt())

                else -> UnexpectedCharacterMessage(
                    codePointToChar(w.charVal),
                    w.lineIndex.toInt(),
                    w.columnIndex.toInt(),
                )
            }
        }

        val points = result.cells.map {
            val pair = it as Pair<*, *>
            val x = if (pair.first is UInt) (pair.first as UInt).toInt() else (pair.first as Int)
            val y = if (pair.second is UInt) (pair.second as UInt).toInt() else (pair.second as Int)
            IntOffset(x, y)
        }.toSet()

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points),
            format = CellStateFormat.FixedFormat.Plaintext,
        )
    }

    @Suppress("UNCHECKED_CAST")
    override fun serializeToString(cellState: CellState): Sequence<String> {
        val minX = cellState.aliveCells.minOfOrNull { it.x } ?: 0
        val maxX = cellState.aliveCells.maxOfOrNull { it.x } ?: 0
        val minY = cellState.aliveCells.minOfOrNull { it.y } ?: 0
        val maxY = cellState.aliveCells.maxOfOrNull { it.y } ?: 0

        val cells = cellState.aliveCells.map { Pair(it.x.toUInt(), it.y.toUInt()) }.toTypedArray()
        val lines = f_Algorithm_serializePlaintext(cells as Array<Any?>, minX, maxX, minY, maxY)
        return lines.asSequence().map { it as String }
    }
}

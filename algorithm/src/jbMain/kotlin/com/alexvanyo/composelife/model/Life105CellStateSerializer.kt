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

@OptIn(ExperimentalUnsignedTypes::class)
object Life105CellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life105

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializeLife105(lines.toList().toTypedArray())

        val warnings = result.warnings.map {
            val w = it as Life105Warning
            when (w.tag) {
                0u -> UnexpectedEmptyFileMessage
                else -> UnexpectedInputMessage(w.line, w.lineIndex.toInt(), w.columnIndex.toInt())
            }
        }

        return when (result.status) {
            0u -> {
                DeserializationResult.Successful(
                    warnings = warnings,
                    cellState = CellState(leanCellsToOffsets(result.cells)),
                    format = CellStateFormat.FixedFormat.Life105,
                )
            }

            1u -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage(result.errLine)),
            )

            2u -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(RuleNotSupportedMessage),
            )

            else -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedInputMessage(
                        result.errLine,
                        result.errLineIndex.toInt(),
                        result.errColumnIndex.toInt(),
                    ),
                ),
            )
        }
    }

    override fun serializeToString(cellState: CellState): Sequence<String> = sequence {
        yield("#Life 1.05")
        yield("#N")

        val remainingCells = cellState.aliveCells.toMutableSet()

        while (remainingCells.isNotEmpty()) {
            val minX = remainingCells.minOf(IntOffset::x)
            val minY = remainingCells.minOf(IntOffset::y)
            val maxY = remainingCells.maxOf(IntOffset::y)

            val rows = f_Algorithm_serializeLife105Block(remainingCells.toLeanCells(), minX, minY, maxY)
            for (row in rows) {
                yield(row as String)
            }
            remainingCells.removeAll { it.x in minX until minX + 80 }
        }
    }
}

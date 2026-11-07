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

@OptIn(ExperimentalUnsignedTypes::class)
object PlaintextCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Plaintext

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializePlaintext(lines.toList().toTypedArray())

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

        val points = leanCellsToOffsets(result.cells)

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points),
            format = CellStateFormat.FixedFormat.Plaintext,
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val minX = cellState.aliveCells.minOfOrNull { it.x } ?: 0
        val maxX = cellState.aliveCells.maxOfOrNull { it.x } ?: 0
        val minY = cellState.aliveCells.minOfOrNull { it.y } ?: 0
        val maxY = cellState.aliveCells.maxOfOrNull { it.y } ?: 0

        val lines = f_Algorithm_serializePlaintext(cellState.aliveCells.toLeanCells(), minX, maxX, minY, maxY)
        return lines.asSequence().map { it as String }
    }
}

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
object Life106CellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life106

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializeLife106(lines.toList().toTypedArray())

        return when (result.status) {
            0u -> {
                DeserializationResult.Successful(
                    warnings = emptyList(),
                    cellState = CellState(leanCellsToOffsets(result.cells)),
                    format = CellStateFormat.FixedFormat.Life106,
                )
            }

            1u -> {
                DeserializationResult.Successful(
                    warnings = listOf(UnexpectedEmptyFileMessage),
                    cellState = emptyCellState(),
                    format = CellStateFormat.FixedFormat.Life106,
                )
            }

            2u -> {
                DeserializationResult.Unsuccessful(
                    warnings = emptyList(),
                    errors = listOf(
                        UnexpectedHeaderMessage(result.errLineContent),
                    ),
                )
            }

            else -> {
                DeserializationResult.Unsuccessful(
                    warnings = emptyList(),
                    errors = listOf(
                        UnexpectedInputMessage(result.errLineContent, result.errLineIndex.toInt(), 0),
                    ),
                )
            }
        }
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val lines = f_Algorithm_serializeLife106(cellState.aliveCells.toLeanCells())
        return lines.asSequence().map { it as String }
    }
}

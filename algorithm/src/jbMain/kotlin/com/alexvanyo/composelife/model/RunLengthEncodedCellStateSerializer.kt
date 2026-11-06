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
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

object RunLengthEncodedCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.RunLengthEncoding

    @Suppress("UNCHECKED_CAST")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val linesArray = lines.toList().toTypedArray()
        val result = f_Algorithm_deserializeRLE(linesArray as Array<Any?>)
        val warnings = result.warnings.map { mapRLEWarning(it as RLEWarning) }

        return when (result.status) {
            0u -> {
                val aliveCells = parseAliveCells(result.cells)
                DeserializationResult.Successful(
                    warnings = warnings,
                    cellState = CellState(aliveCells),
                    format = CellStateFormat.FixedFormat.RunLengthEncoding,
                )
            }

            1u -> {
                DeserializationResult.Successful(
                    warnings = warnings,
                    cellState = emptyCellState(),
                    format = CellStateFormat.FixedFormat.RunLengthEncoding,
                )
            }

            2u -> {
                DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(UnexpectedHeaderMessage(result.errLine)),
                )
            }

            3u -> {
                DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(RuleNotSupportedMessage),
                )
            }

            else -> {
                DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(
                        UnexpectedInputMessage(
                            input = result.errLine,
                            lineIndex = result.errLineIndex.toInt(),
                            characterIndex = result.errColumnIndex.toInt(),
                        ),
                    ),
                )
            }
        }
    }

    private fun mapRLEWarning(warn: RLEWarning): ParameterizedString = when (warn.tag) {
        0u -> UnexpectedEmptyFileMessage

        1u -> DuplicateTopLeftCoordinateMessage(IntOffset(warn.offsetX, warn.offsetY))

        2u -> UnexpectedCharacterMessage(
            character = codePointToChar(warn.charVal),
            lineIndex = warn.lineIndex.toInt(),
            characterIndex = warn.columnIndex.toInt(),
        )

        3u -> UnexpectedInputMessage(
            input = warn.strVal,
            lineIndex = warn.lineIndex.toInt(),
            characterIndex = warn.columnIndex.toInt(),
        )

        else -> UnexpectedInputMessage(
            input = "IndexedValue(index=${warn.columnIndex - 1u}, value=${codePointToChar(warn.charVal)})",
            lineIndex = warn.lineIndex.toInt(),
            characterIndex = warn.columnIndex.toInt(),
        )
    }

    private fun parseAliveCells(cells: Array<Any?>): Set<IntOffset> = cells.map {
        val pair = it as Pair<*, *>
        val cellX = if (pair.first is UInt) (pair.first as UInt).toInt() else (pair.first as Int)
        val cellY = if (pair.second is UInt) (pair.second as UInt).toInt() else (pair.second as Int)
        IntOffset(cellX, cellY)
    }.toSet()

    @Suppress("UNCHECKED_CAST")
    override fun serializeToString(cellState: CellState): Sequence<String> {
        val boundingBox = cellState.boundingBox
        val cells = cellState.aliveCells.map { Pair(it.x.toUInt(), it.y.toUInt()) }.toTypedArray()
        val minX = boundingBox.left
        val maxX = boundingBox.right - 1
        val minY = boundingBox.top
        val maxY = boundingBox.bottom - 1
        val lines = f_Algorithm_serializeRLE(cells as Array<Any?>, minX, maxX, minY, maxY)
        return lines.asSequence().map { it as String }
    }
}

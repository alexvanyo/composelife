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

object MacrocellCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Macrocell

    @Suppress("UNCHECKED_CAST")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val linesArray = lines.toList().toTypedArray()
        val result = f_Algorithm_deserializeMacrocell(linesArray as Array<Any?>)
        val warnings = result.warnings.map { mapMacrocellWarning(it as MacrocellWarning) }

        return when (result.status) {
            0u -> {
                DeserializationResult.Successful(
                    warnings = warnings,
                    cellState = HashLifeCellState(
                        offset = IntOffset.Zero,
                        macroCell = result.macroCell,
                    ),
                    format = CellStateFormat.FixedFormat.Macrocell,
                )
            }

            1u -> {
                DeserializationResult.Successful(
                    warnings = listOf(UnexpectedEmptyFileMessage),
                    cellState = emptyCellState(),
                    format = CellStateFormat.FixedFormat.Macrocell,
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
                    errors = listOf(
                        UnexpectedInputMessage(
                            input = result.errLine,
                            lineIndex = result.errLineIndex.toInt(),
                            characterIndex = result.errColIndex.toInt(),
                        ),
                    ),
                )
            }

            else -> {
                DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(
                        UnexpectedNodeIdMessage(
                            lineIndex = result.errLineIndex.toInt(),
                            characterIndices = result.errRangeStart.toInt()..result.errRangeEnd.toInt(),
                        ),
                    ),
                )
            }
        }
    }

    private fun mapMacrocellWarning(warn: MacrocellWarning): ParameterizedString = when (warn.tag) {
        0u -> UnexpectedEmptyFileMessage

        1u -> UnexpectedBlankLineMessage(warn.lineIndex.toInt())

        else -> UnexpectedInputMessage(
            input = warn.input,
            lineIndex = warn.lineIndex.toInt(),
            characterIndex = warn.columnIndex.toInt(),
        )
    }

    @Suppress("UNCHECKED_CAST")
    override fun serializeToString(cellState: CellState): Sequence<String> {
        val hashLifeCellState = cellState.toHashLifeCellState()
        val lines = f_Algorithm_serializeMacrocell(hashLifeCellState.macroCell)
        return lines.asSequence().map { it as String }
    }
}

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
            when (val warning = it as PlaintextWarning) {
                is PlaintextWarning.BlankLine -> UnexpectedBlankLineMessage(warning.lineIndex.toInt())

                is PlaintextWarning.ShortLine -> UnexpectedShortLineMessage(warning.lineIndex.toInt())

                is PlaintextWarning.UnexpectedChar -> UnexpectedCharacterMessage(
                    codePointToChar(warning.codePoint),
                    warning.lineIndex.toInt(),
                    warning.columnIndex.toInt(),
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

    override fun serializeToString(cellState: CellState): Sequence<String> =
        f_Algorithm_serializePlaintextCells(cellState.aliveCells.toLeanCells()).asSequence().map { it as String }
}

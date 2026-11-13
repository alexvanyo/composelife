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

@OptIn(ExperimentalUnsignedTypes::class)
object RunLengthEncodedCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.RunLengthEncoding

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializeRLE(lines.toList().toTypedArray())
        val warnings = result.warnings.map { mapRLEWarning(it as RLEWarning) }

        return when (val status = result.status) {
            is RLEStatus.Ok -> DeserializationResult.Successful(
                warnings = warnings,
                cellState = CellState(leanCellsToOffsets(result.cells)),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            )

            is RLEStatus.EmptyFile -> DeserializationResult.Successful(
                warnings = warnings,
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            )

            is RLEStatus.InvalidHeader -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage(status.line)),
            )

            is RLEStatus.RuleNotSupported -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(RuleNotSupportedMessage),
            )

            is RLEStatus.UnexpectedInput -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedInputMessage(
                        input = status.input,
                        lineIndex = status.lineIndex.toInt(),
                        characterIndex = status.columnIndex.toInt(),
                    ),
                ),
            )
        }
    }

    private fun mapRLEWarning(warning: RLEWarning): ParameterizedString = when (warning) {
        is RLEWarning.EmptyFile -> UnexpectedEmptyFileMessage

        is RLEWarning.DuplicateOffset -> DuplicateTopLeftCoordinateMessage(IntOffset(warning.x, warning.y))

        is RLEWarning.UnexpectedChar -> UnexpectedCharacterMessage(
            character = codePointToChar(warning.codePoint),
            lineIndex = warning.lineIndex.toInt(),
            characterIndex = warning.columnIndex.toInt(),
        )

        is RLEWarning.UnexpectedInput -> UnexpectedInputMessage(
            input = warning.input,
            lineIndex = warning.lineIndex.toInt(),
            characterIndex = warning.columnIndex.toInt(),
        )

        is RLEWarning.CharAfterEnd -> UnexpectedInputMessage(
            input = "IndexedValue(index=${warning.columnIndex - 1u}, value=${codePointToChar(warning.codePoint)})",
            lineIndex = warning.lineIndex.toInt(),
            characterIndex = warning.columnIndex.toInt(),
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> =
        f_Algorithm_serializeRLECells(cellState.aliveCells.toLeanCells()).asSequence().map { it as String }
}

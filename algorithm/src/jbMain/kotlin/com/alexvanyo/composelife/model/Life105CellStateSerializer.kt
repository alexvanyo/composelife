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
object Life105CellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life105

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializeLife105(lines.toList().toTypedArray())

        val warnings = result.warnings.map {
            when (val warning = it as Life105Warning) {
                is Life105Warning.EmptyFile -> UnexpectedEmptyFileMessage

                is Life105Warning.UnexpectedInput -> UnexpectedInputMessage(
                    warning.line,
                    warning.lineIndex.toInt(),
                    warning.columnIndex.toInt(),
                )
            }
        }

        return when (val status = result.status) {
            is Life105Status.Ok -> DeserializationResult.Successful(
                warnings = warnings,
                cellState = CellState(leanCellsToOffsets(result.cells)),
                format = CellStateFormat.FixedFormat.Life105,
            )

            is Life105Status.InvalidHeader -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage(status.line)),
            )

            is Life105Status.RuleNotSupported -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(RuleNotSupportedMessage),
            )

            is Life105Status.UnexpectedInput -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedInputMessage(status.line, status.lineIndex.toInt(), status.columnIndex.toInt()),
                ),
            )
        }
    }

    override fun serializeToString(cellState: CellState): Sequence<String> =
        f_Algorithm_serializeLife105(cellState.aliveCells.toLeanCells()).asSequence().map { it as String }
}

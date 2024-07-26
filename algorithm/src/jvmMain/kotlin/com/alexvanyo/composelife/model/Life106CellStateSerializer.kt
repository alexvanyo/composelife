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

object Life106CellStateSerializer : FixedFormatCellStateSerializer {

    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life106

    @Suppress("ReturnCount")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        var lineIndex = 0

        val iterator = lines.iterator()

        if (!iterator.hasNext()) {
            warnings.add(UnexpectedEmptyFileMessage())

            return DeserializationResult.Successful(
                warnings = warnings,
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.Life106,
            )
        }

        val headerLine = iterator.next()
        if (headerLine != "#Life 1.06") {
            return DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedHeaderMessage(headerLine),
                ),
            )
        }
        lineIndex++

        val aliveCells = mutableSetOf<IntOffset>()

        while (iterator.hasNext()) {
            val line = iterator.next()

            val matchResult = Regex("""(\d+) (\d+)""").matchEntire(line)

            if (matchResult == null) {
                return DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(
                        UnexpectedInputMessage(line, lineIndex + 1, 0),
                    ),
                )
            } else {
                val x = matchResult.groupValues[1].toInt()
                val y = matchResult.groupValues[2].toInt()
                aliveCells.add(IntOffset(x, y))
            }
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(aliveCells),
            format = CellStateFormat.FixedFormat.Life106,
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> = sequence {
        yield("#Life 1.06")
        yieldAll(cellState.aliveCells.map { "${it.x} ${it.y}" })
    }
}

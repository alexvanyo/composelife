/*
 * Copyright 2022 The Android Open Source Project
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
import com.alexvanyo.composelife.algorithm.R
import com.alexvanyo.composelife.model.CellStateSerializer.DeserializationResult
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.livefront.sealedenum.GenSealedEnum

interface CellStateSerializer {
    fun deserializeToCellState(lines: Sequence<String>): DeserializationResult

    fun serializeToString(cellState: CellState): Sequence<String>

    sealed interface DeserializationResult {
        val warnings: List<ParameterizedString>

        data class Successful(
            override val warnings: List<ParameterizedString>,
            val cellState: CellState,
        ) : DeserializationResult

        data class Unsuccessful(
            override val warnings: List<ParameterizedString>,
            val errors: List<ParameterizedString>,
        ) : DeserializationResult
    }
}

sealed interface CellStateFormat {

    sealed interface FixedFormat {
        object Plaintext : CellStateFormat

        @GenSealedEnum(generateEnum = true)
        companion object
    }

    @GenSealedEnum(generateEnum = true)
    companion object
}

class PlaintextCellStateSerializer : CellStateSerializer {

    @Suppress("LongMethod")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        val points = mutableSetOf<IntOffset>()

        var expectedRowLength: Int? = null
        var longestLineIndex: Int? = null

        var lineIndex = 0
        var rowIndex = 0

        val iterator = lines.iterator()

        while (iterator.hasNext()) {
            val line = iterator.next()

            when (line.firstOrNull()) {
                '!' -> {
                    // Comment line, continue
                }
                null -> {
                    if (iterator.hasNext()) {
                        warnings.add(ParameterizedString(R.string.unexpected_blank_line, lineIndex + 1))
                    }
                }
                else -> {
                    if (expectedRowLength == null) {
                        expectedRowLength = line.length
                        longestLineIndex = lineIndex
                    } else if (line.length > expectedRowLength) {
                        // Guaranteed non-null since expectedRowLength is non-null
                        @Suppress("UnsafeCallOnNullableType")
                        warnings.add(ParameterizedString(R.string.unexpected_short_line, longestLineIndex!! + 1))
                        expectedRowLength = line.length
                        longestLineIndex = lineIndex
                    } else if (line.length < expectedRowLength) {
                        warnings.add(ParameterizedString(R.string.unexpected_short_line, lineIndex + 1))
                    }

                    points.addAll(
                        line.withIndex()
                            .filter { (columnIndex, c) ->
                                when (c) {
                                    '.' -> false
                                    'O' -> true
                                    else -> {
                                        warnings.add(
                                            ParameterizedString(
                                                R.string.unexpected_character,
                                                c,
                                                lineIndex + 1,
                                                columnIndex + 1,
                                            ),
                                        )
                                        when (c) {
                                            ' ' -> false
                                            else -> true
                                        }
                                    }
                                }
                            }
                            .map { (columnIndex, _) -> IntOffset(columnIndex, rowIndex) },
                    )

                    rowIndex++
                }
            }

            lineIndex++
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points),
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val minX = cellState.aliveCells.map { it.x }.minOrNull() ?: 0
        val maxX = cellState.aliveCells.map { it.x }.maxOrNull() ?: 0
        val minY = cellState.aliveCells.map { it.y }.minOrNull() ?: 0
        val maxY = cellState.aliveCells.map { it.y }.maxOrNull() ?: 0

        return sequence {
            (minY..maxY).forEach { y ->
                val line = buildString {
                    (minX..maxX).forEach { x ->
                        append(
                            if (IntOffset(x, y) in cellState.aliveCells) {
                                'O'
                            } else {
                                '.'
                            },
                        )
                    }
                }
                yield("$line\n")
            }
        }
    }
}

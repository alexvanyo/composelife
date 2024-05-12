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

object Life105CellStateSerializer : FixedFormatCellStateSerializer {

    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life105

    @Suppress("LongMethod", "ComplexMethod", "NestedBlockDepth", "ReturnCount")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        var lineIndex = 0

        val iterator = lines.iterator()

        if (!iterator.hasNext()) {
            warnings.add(UnexpectedEmptyFileMessage())

            return DeserializationResult.Successful(
                warnings = warnings,
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.Life105,
            )
        }

        val headerLine = iterator.next()
        if (headerLine != "#Life 1.05") {
            return DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedHeaderMessage(headerLine),
                ),
            )
        }
        lineIndex++

        var lineAfterDescriptions: String? = null
        while (
            run {
                if (iterator.hasNext()) {
                    val line = iterator.next()
                    lineAfterDescriptions = line
                    line.startsWith("#D")
                } else {
                    false
                }
            }
        ) {
            // Ignore description lines
            lineIndex++
        }

        val ruleIterator = iterator {
            lineAfterDescriptions?.let { yield(it) }
            yieldAll(iterator)
        }

        val lineAfterRule = if (ruleIterator.hasNext()) {
            val line = ruleIterator.next()
            if (line.startsWith("#N")) {
                if (line != "#N") {
                    warnings.add(UnexpectedInputMessage(line, lineIndex + 1, 3))
                }
                // Normal ruleset, continue
                lineIndex++
                null
            } else if (line.startsWith("#R")) {
                val ruleRegex = Regex("""#R (\d+)/(\d+)""")
                val matchResult = ruleRegex.matchEntire(line)
                if (matchResult == null) {
                    return DeserializationResult.Unsuccessful(
                        warnings = warnings,
                        errors = listOf(
                            UnexpectedInputMessage(line, lineIndex + 1, 3),
                        ),
                    )
                } else {
                    val survival = matchResult.groupValues[1].map { it.digitToInt() }.toSet()
                    val birth = matchResult.groupValues[2].map { it.digitToInt() }.toSet()

                    if (survival != setOf(2, 3) || birth != setOf(3)) {
                        return DeserializationResult.Unsuccessful(
                            warnings = warnings,
                            errors = listOf(RuleNotSupportedMessage()),
                        )
                    } else {
                        lineIndex++
                        null
                    }
                }
            } else {
                line
            }
        } else {
            null
        }

        val blockIterator = iterator {
            lineAfterRule?.let { yield(it) }
            yieldAll(ruleIterator)
        }

        val points = mutableSetOf<IntOffset>()

        var blockOffset: IntOffset? = null
        var rowIndex = 0

        val blockRegex = Regex("""#P (-?\d+) (-?\d+)""")
        val rowRegex = Regex("""[.*]+""")

        while (blockIterator.hasNext()) {
            val line = blockIterator.next()

            when {
                line.startsWith("#P") -> {
                    val matchResult = blockRegex.matchEntire(line)
                    if (matchResult == null) {
                        return DeserializationResult.Unsuccessful(
                            warnings = warnings,
                            errors = listOf(
                                UnexpectedInputMessage(line, lineIndex + 1, 3),
                            ),
                        )
                    } else {
                        val x = matchResult.groupValues[1].toInt()
                        val y = matchResult.groupValues[2].toInt()
                        blockOffset = IntOffset(x, y)
                        rowIndex = 0
                    }
                }
                rowRegex.matches(line) -> {
                    val currentBlockOffset = blockOffset
                    if (currentBlockOffset == null) {
                        return DeserializationResult.Unsuccessful(
                            warnings = warnings,
                            errors = listOf(
                                UnexpectedInputMessage(line, lineIndex + 1, 1),
                            ),
                        )
                    } else {
                        points.addAll(
                            line.withIndex()
                                .filter { (_, c) ->
                                    when (c) {
                                        '.' -> false
                                        '*' -> true
                                        else -> error("Characters should not occur due to matched regex!")
                                    }
                                }
                                .map { (columnIndex, _) -> IntOffset(columnIndex, rowIndex) + currentBlockOffset },
                        )

                        rowIndex++
                    }
                }
                else -> {
                    return DeserializationResult.Unsuccessful(
                        warnings = warnings,
                        errors = listOf(
                            UnexpectedInputMessage(line, lineIndex + 1, 1),
                        ),
                    )
                }
            }

            lineIndex++
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points),
            format = CellStateFormat.FixedFormat.Life105,
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> = sequence {
        yield("#Life 1.05")
        yield("#N")

        val remainingCells = cellState.aliveCells.toMutableSet()

        // Brute-force implementation: find the remaining top-left-most point to use as a block offset, and emit all
        // points we can in that block
        while (remainingCells.isNotEmpty()) {
            val minX = remainingCells.minOf(IntOffset::x)
            val minY = remainingCells.minOf(IntOffset::y)
            val maxY = remainingCells.maxOf(IntOffset::y)

            yield("#P $minX $minY")
            for (y in minY..maxY) {
                yield(
                    buildString {
                        for (x in minX until minX + 80) {
                            val offset = IntOffset(x, y)
                            if (offset in remainingCells) {
                                append("*")
                                remainingCells.remove(offset)
                            } else {
                                append(".")
                            }
                        }
                    },
                )
            }
        }
    }
}

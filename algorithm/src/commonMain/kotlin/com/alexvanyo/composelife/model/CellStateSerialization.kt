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
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.withContext
import javax.inject.Inject

interface FixedFormatCellStateSerializer {
    fun deserializeToCellState(lines: Sequence<String>): DeserializationResult

    fun serializeToString(cellState: CellState): Sequence<String>
}

interface CellStateSerializer {
    suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult

    suspend fun serializeToString(
        format: CellStateFormat.FixedFormat,
        cellState: CellState,
    ): Sequence<String>
}

class FlexibleCellStateSerializer @Inject constructor(
    private val dispatchers: ComposeLifeDispatchers,
) : CellStateSerializer {
    override suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult = @Suppress("InjectDispatcher")
    withContext(dispatchers.Default) {
        val targetedSerializer = when (format) {
            CellStateFormat.FixedFormat.Plaintext -> PlaintextCellStateSerializer
            CellStateFormat.FixedFormat.Life105 -> Life105CellStateSerializer
            CellStateFormat.FixedFormat.Life106,
            CellStateFormat.FixedFormat.RunLengthEncoding,
            CellStateFormat.Life,
            CellStateFormat.Unknown,
            -> null
        }

        when (val targetedResult = targetedSerializer?.deserializeToCellState(lines)) {
            is DeserializationResult.Successful -> return@withContext targetedResult
            is DeserializationResult.Unsuccessful,
            null,
            -> Unit
        }

        val allSerializers = listOf(
            PlaintextCellStateSerializer,
            Life105CellStateSerializer,
        )

        coroutineScope {
            allSerializers
                .map {
                    async {
                        it.deserializeToCellState(lines)
                    }
                }
                .awaitAll()
                .reduce { a, b ->
                    when (a) {
                        is DeserializationResult.Unsuccessful -> b
                        is DeserializationResult.Successful -> {
                            when (b) {
                                is DeserializationResult.Successful -> if (a.warnings.isEmpty()) {
                                    a
                                } else {
                                    b
                                }
                                is DeserializationResult.Unsuccessful -> a
                            }
                        }
                    }
                }
        }
    }

    override suspend fun serializeToString(
        format: CellStateFormat.FixedFormat,
        cellState: CellState,
    ): Sequence<String> =
        when (format) {
            CellStateFormat.FixedFormat.Plaintext -> PlaintextCellStateSerializer
            CellStateFormat.FixedFormat.Life105 -> Life105CellStateSerializer
            CellStateFormat.FixedFormat.Life106,
            CellStateFormat.FixedFormat.RunLengthEncoding,
            -> TODO("Format not implemented yet!")
        }.serializeToString(cellState)
}

object PlaintextCellStateSerializer : FixedFormatCellStateSerializer {

    private data class LineLengthInfo(
        val index: Int,
        val length: Int,
    )

    @Suppress("LongMethod")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        val points = mutableSetOf<IntOffset>()

        var longestLine: LineLengthInfo? = null

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
                        warnings.add(UnexpectedBlankLineMessage(lineIndex + 1))
                    }
                }
                else -> {
                    if (longestLine == null) {
                        longestLine = LineLengthInfo(
                            index = lineIndex,
                            length = line.length,
                        )
                    } else if (line.length > longestLine.length) {
                        warnings.add(UnexpectedShortLineMessage(longestLine.index + 1))
                        longestLine = LineLengthInfo(
                            index = lineIndex,
                            length = line.length,
                        )
                    } else if (line.length < longestLine.length) {
                        warnings.add(UnexpectedShortLineMessage(lineIndex + 1))
                    }

                    points.addAll(
                        line.withIndex()
                            .filter { (columnIndex, c) ->
                                when (c) {
                                    '.' -> false
                                    'O' -> true
                                    else -> {
                                        warnings.add(
                                            UnexpectedCharacterMessage(
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
        val minX = cellState.aliveCells.minOfOrNull { it.x } ?: 0
        val maxX = cellState.aliveCells.maxOfOrNull { it.x } ?: 0
        val minY = cellState.aliveCells.minOfOrNull { it.y } ?: 0
        val maxY = cellState.aliveCells.maxOfOrNull { it.y } ?: 0

        return sequence {
            (minY..maxY).forEach { y ->
                yield(
                    buildString {
                        (minX..maxX).forEach { x ->
                            append(
                                if (IntOffset(x, y) in cellState.aliveCells) {
                                    'O'
                                } else {
                                    '.'
                                },
                            )
                        }
                    },
                )
            }
        }
    }
}

object Life105CellStateSerializer : FixedFormatCellStateSerializer {

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
            (minY..maxY).forEach { y ->
                yield(
                    buildString {
                        (minX until minX + 80).forEach { x ->
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

fun String.toCellState(
    topLeftOffset: IntOffset = IntOffset.Zero,
    fixedFormatCellStateSerializer: FixedFormatCellStateSerializer = PlaintextCellStateSerializer,
    throwOnWarnings: Boolean = true,
): CellState {
    val deserializationResult = trimMargin()
        .split("\n")
        .asSequence()
        .run(fixedFormatCellStateSerializer::deserializeToCellState)

    return when (deserializationResult) {
        is DeserializationResult.Successful -> {
            check(deserializationResult.warnings.isEmpty() || !throwOnWarnings) {
                "Warnings when parsing cell state!"
            }
            deserializationResult.cellState.offsetBy(topLeftOffset)
        }
        is DeserializationResult.Unsuccessful ->
            error("Could not parse cell state!")
    }
}

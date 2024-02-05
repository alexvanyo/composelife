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
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.withContext
import me.tatarka.inject.annotations.Inject

/**
 * A serializer for a [CellStateFormat.FixedFormat].
 *
 * This can directly and synchronously deserialize a sequence of lines into a [DeserializationResult] with
 * [deserializeToCellState], and serialize a [CellState] into a sequence of lines with [serializeToString].
 */
interface FixedFormatCellStateSerializer {
    val format: CellStateFormat.FixedFormat

    fun deserializeToCellState(lines: Sequence<String>): DeserializationResult

    fun serializeToString(cellState: CellState): Sequence<String>
}

/**
 * A general [CellStateSerializer] that can asynchronously serialize and deserialize with a given format.
 */
interface CellStateSerializer {

    /**
     * Attempts to deserialize the sequence of lines into a [DeserializationResult] for the given [CellStateFormat].
     *
     * If format is not a [CellStateFormat.FixedFormat], or if deserialization with the given
     * [CellStateFormat.FixedFormat] fails, then an attempt will be made to deserialize lines with
     * multiple formats.
     */
    suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult

    /**
     * Serializes the [CellState] into a sequence of lines with the given [CellStateFormat.FixedFormat].
     *
     * Note that format
     */
    suspend fun serializeToString(
        format: CellStateFormat.FixedFormat,
        cellState: CellState,
    ): Sequence<String>
}

@Inject
class FlexibleCellStateSerializer(
    private val dispatchers: ComposeLifeDispatchers,
) : CellStateSerializer {
    override suspend fun deserializeToCellState(
        format: CellStateFormat,
        lines: Sequence<String>,
    ): DeserializationResult =
        @Suppress("InjectDispatcher")
        withContext(dispatchers.Default) {
            val targetedSerializer = when (format) {
                CellStateFormat.FixedFormat.Plaintext -> PlaintextCellStateSerializer
                CellStateFormat.FixedFormat.Life105 -> Life105CellStateSerializer
                CellStateFormat.FixedFormat.RunLengthEncoding -> RunLengthEncodedCellStateSerializer
                CellStateFormat.FixedFormat.Life106,
                CellStateFormat.Life,
                CellStateFormat.Unknown,
                -> null
            }

            val targetedResult = targetedSerializer?.deserializeToCellState(lines)
            when (targetedResult) {
                is DeserializationResult.Successful -> return@withContext targetedResult
                is DeserializationResult.Unsuccessful,
                null,
                -> Unit
            }

            val allSerializers = listOf(
                PlaintextCellStateSerializer,
                Life105CellStateSerializer,
                RunLengthEncodedCellStateSerializer,
            )

            coroutineScope {
                allSerializers
                    .map {
                        if (it == targetedSerializer) {
                            CompletableDeferred(checkNotNull(targetedResult))
                        } else {
                            async {
                                it.deserializeToCellState(lines)
                            }
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
            CellStateFormat.FixedFormat.RunLengthEncoding -> RunLengthEncodedCellStateSerializer
            CellStateFormat.FixedFormat.Life106 -> TODO("Format not implemented yet!")
        }.serializeToString(cellState)
}

object PlaintextCellStateSerializer : FixedFormatCellStateSerializer {

    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Plaintext

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
            format = CellStateFormat.FixedFormat.Plaintext,
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val minX = cellState.aliveCells.minOfOrNull { it.x } ?: 0
        val maxX = cellState.aliveCells.maxOfOrNull { it.x } ?: 0
        val minY = cellState.aliveCells.minOfOrNull { it.y } ?: 0
        val maxY = cellState.aliveCells.maxOfOrNull { it.y } ?: 0

        return sequence {
            for (y in minY..maxY) {
                yield(
                    buildString {
                        for (x in minX..maxX) {
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

object RunLengthEncodedCellStateSerializer : FixedFormatCellStateSerializer {

    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.RunLengthEncoding

    @Suppress("LongMethod", "ReturnCount", "CyclomaticComplexMethod", "NestedBlockDepth")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()
        var lineIndex = 0

        val iterator = lines.iterator()

        if (!iterator.hasNext()) {
            warnings.add(UnexpectedEmptyFileMessage())

            return DeserializationResult.Successful(
                warnings = warnings,
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            )
        }

        var offset: IntOffset? = null

        var lineAfterComments: String?
        while (
            run {
                if (iterator.hasNext()) {
                    val line = iterator.next()
                    lineAfterComments = line

                    val offsetRegex = Regex("""#[RP] (-?\d+) (-?\d+)""")
                    val matchResult = offsetRegex.matchEntire(line)
                    if (matchResult != null) {
                        val x = matchResult.groupValues[1].toInt()
                        val y = matchResult.groupValues[2].toInt()
                        val newOffset = IntOffset(x, y)
                        if (offset != null) {
                            warnings.add(DuplicateTopLeftCoordinateMessage(newOffset))
                        }
                        offset = newOffset
                    }

                    line.startsWith("#")
                } else {
                    lineAfterComments = null
                    false
                }
            }
        ) {
            lineIndex++
        }

        val headerLine = lineAfterComments
        val headerRegexWithoutRule = Regex("""x = (\d+), y = (\d+)""")
        val headerRegexWithRuleFormat1 = Regex("""x = (\d+), y = (\d+), rule = B(\d+)/S(\d+)""")
        val headerRegexWithRuleFormat2 = Regex("""x = (\d+), y = (\d+), rule = (\d+)/(\d+)""")

        if (headerLine == null) {
            return DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage("none")),
            )
        }

        val withoutRuleMatchResult = headerRegexWithoutRule.matchEntire(headerLine)
        val withRuleFormat1MatchResult = headerRegexWithRuleFormat1.matchEntire(headerLine)
        val withRuleFormat2MatchResult = headerRegexWithRuleFormat2.matchEntire(headerLine)

        @Suppress("ASSIGNED_BUT_NEVER_ACCESSED_VARIABLE")
        val size: IntSize

        if (withoutRuleMatchResult != null) {
            val width = withoutRuleMatchResult.groupValues[1].toInt()
            val height = withoutRuleMatchResult.groupValues[2].toInt()
            @Suppress("UNUSED_VALUE")
            size = IntSize(width, height)
        } else if (withRuleFormat1MatchResult != null) {
            val width = withRuleFormat1MatchResult.groupValues[1].toInt()
            val height = withRuleFormat1MatchResult.groupValues[2].toInt()
            @Suppress("UNUSED_VALUE")
            size = IntSize(width, height)

            val birth = withRuleFormat1MatchResult.groupValues[3].map { it.digitToInt() }.toSet()
            val survival = withRuleFormat1MatchResult.groupValues[4].map { it.digitToInt() }.toSet()

            if (survival != setOf(2, 3) || birth != setOf(3)) {
                return DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(RuleNotSupportedMessage()),
                )
            }
        } else if (withRuleFormat2MatchResult != null) {
            val width = withRuleFormat2MatchResult.groupValues[1].toInt()
            val height = withRuleFormat2MatchResult.groupValues[2].toInt()
            @Suppress("UNUSED_VALUE")
            size = IntSize(width, height)

            val birth = withRuleFormat2MatchResult.groupValues[4].map { it.digitToInt() }.toSet()
            val survival = withRuleFormat2MatchResult.groupValues[3].map { it.digitToInt() }.toSet()

            if (survival != setOf(2, 3) || birth != setOf(3)) {
                return DeserializationResult.Unsuccessful(
                    warnings = warnings,
                    errors = listOf(RuleNotSupportedMessage()),
                )
            }
        } else {
            return DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage(headerLine)),
            )
        }
        lineIndex++

        val itemSequence = sequence {
            while (iterator.hasNext()) {
                val line = iterator.next()
                val charIterator = line.asSequence().withIndex().iterator()
                var countString = StringBuilder()

                while (charIterator.hasNext()) {
                    val (charIndex, char) = charIterator.next()
                    if (char.isDigit()) {
                        countString.append(char)
                    } else if (char == '$') {
                        val rowEndCount = if (countString.isEmpty()) 1 else countString.toString().toInt()
                        repeat(rowEndCount) {
                            yield(RunItem.RowEnd)
                        }
                        countString = StringBuilder()
                    } else if (char == '!') {
                        if (countString.isNotEmpty()) {
                            warnings.add(
                                UnexpectedInputMessage(
                                    input = "$countString$char",
                                    lineIndex = lineIndex + 1,
                                    characterIndex = charIndex + 1 - countString.length,
                                ),
                            )
                        }
                        if (charIterator.hasNext()) {
                            warnings.add(
                                UnexpectedInputMessage(
                                    input = "${charIterator.next()}",
                                    lineIndex = lineIndex + 1,
                                    characterIndex = charIndex + 2,
                                ),
                            )
                        } else if (iterator.hasNext()) {
                            warnings.add(
                                UnexpectedInputMessage(
                                    input = iterator.next(),
                                    lineIndex = lineIndex + 2,
                                    characterIndex = 1,
                                ),
                            )
                        }
                        yield(RunItem.RowEnd)
                        return@sequence
                    } else if (char == 'b') {
                        yield(RunItem.DeadRun(if (countString.isEmpty()) 1 else countString.toString().toInt()))
                        countString = StringBuilder()
                    } else {
                        if (char != 'o') {
                            warnings.add(
                                UnexpectedCharacterMessage(
                                    character = char,
                                    lineIndex = lineIndex + 1,
                                    characterIndex = charIndex + 1,
                                ),
                            )
                        }
                        yield(RunItem.AliveRun(if (countString.isEmpty()) 1 else countString.toString().toInt()))
                        countString = StringBuilder()
                    }
                }

                lineIndex++
            }
        }

        val points = mutableSetOf<IntOffset>()
        var y = offset?.y ?: 0
        var x = offset?.x ?: 0

        val itemIterator = itemSequence.iterator()
        while (itemIterator.hasNext()) {
            val item = itemIterator.next()
            if (item.value == null) {
                y++
                x = offset?.x ?: 0
            } else {
                val (state, count) = item.value
                if (state) {
                    for (it in x until x + count) {
                        points.add(IntOffset(it, y))
                    }
                }
                x += count
            }
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = CellState(points),
            format = CellStateFormat.FixedFormat.RunLengthEncoding,
        )
    }

    @JvmInline
    private value class RunItem private constructor(val value: Pair<Boolean, Int>?) {
        companion object {
            val RowEnd = RunItem(null)
            fun AliveRun(count: Int) = RunItem(true to count)
            fun DeadRun(count: Int) = RunItem(false to count)
        }
    }

    override fun serializeToString(cellState: CellState): Sequence<String> = sequence {
        val boundingBox = cellState.boundingBox

        yield("#R ${boundingBox.left} ${boundingBox.top}")
        yield("x = ${boundingBox.width}, y = ${boundingBox.height}, rule = B3/S23")

        /**
         * The direct sequence of raw tags, without run length encoding optimizations applied (yet)
         */
        val tagSequence = sequence {
            for (y in boundingBox.top until boundingBox.bottom) {
                for (x in boundingBox.left until boundingBox.right) {
                    val cell = IntOffset(x, y)
                    yield(if (cell in cellState.aliveCells) "o" else "b")
                }
                // Yield the line end if it isn't the last line
                if (y != boundingBox.bottom - 1) {
                    yield("$")
                }
            }
            yield("!")
        }

        /**
         * The sequence of items that can't be broken apart with line breaks
         */
        val runLengthEncodedItemSequence = tagSequence.runLengthEncode()

        /**
         * The optimized sequence of items that can't be broken apart with line breaks, removing ones that aren't
         * needed.
         */
        val optimizedRunLengthEncodedItemSequence = sequence {
            val iterator = runLengthEncodedItemSequence.iterator()

            var currentItem = iterator.next()

            while (iterator.hasNext()) {
                val nextItem = iterator.next()
                val currentItemLast = currentItem.last()
                val nextItemLast = nextItem.last()

                // We can skip emitting dead space at the end of a line
                val isDeadSpaceAtEndOfLine = currentItemLast == 'b' && (nextItemLast == '$' || nextItemLast == '!')
                if (!isDeadSpaceAtEndOfLine) {
                    yield(currentItem)
                }

                currentItem = nextItem
            }

            // Yield the last item
            yield(currentItem)
        }
            // Run length encode again, to combine line breaks for fully empty lines
            .runLengthEncode()

        val lineSequence = sequence {
            val itemIterator = optimizedRunLengthEncodedItemSequence.iterator()
            var line = StringBuilder()

            while (itemIterator.hasNext()) {
                val item = itemIterator.next()
                // If the new item would make us exceed a line length of 70, yield the line
                if (item.length + line.length > 70) {
                    yield(line.toString())
                    line = StringBuilder()
                }
                line.append(item)
            }
            // Yield the last line
            yield(line.toString())
        }

        yieldAll(lineSequence)
    }
}

private fun parseRunLengthEncodedItem(item: String): Pair<Char, Int> =
    item.last() to if (item.length == 1) 1 else item.dropLast(1).toInt()

private fun Sequence<String>.runLengthEncode(): Sequence<String> = sequence {
    val iterator = iterator()

    var (currentChar, currentCount) = parseRunLengthEncodedItem(iterator.next())

    suspend fun SequenceScope<String>.yieldRun() {
        yield(
            buildString {
                // We can omit the number if the run count is 1
                if (currentCount > 1) {
                    append("$currentCount")
                }
                append(currentChar)
            },
        )
    }

    while (iterator.hasNext()) {
        val (nextChar, nextCount) = parseRunLengthEncodedItem(iterator.next())
        if (nextChar == currentChar) {
            // If the run continues, increase the count and continue
            currentCount += nextCount
        } else {
            // If the run stopped, yield it, and swap to the new state with the next count seen
            yieldRun()
            currentChar = nextChar
            currentCount = nextCount
        }
    }

    // Yield the last run
    yieldRun()
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
                "Warnings when parsing cell state!\n" + deserializationResult.warnings.joinToString("\n")
            }
            deserializationResult.cellState.offsetBy(topLeftOffset)
        }
        is DeserializationResult.Unsuccessful ->
            error("Could not parse cell state!\n" + deserializationResult.errors.joinToString("\n"))
    }
}

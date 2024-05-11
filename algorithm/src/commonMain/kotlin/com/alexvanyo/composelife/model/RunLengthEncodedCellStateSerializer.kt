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
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

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

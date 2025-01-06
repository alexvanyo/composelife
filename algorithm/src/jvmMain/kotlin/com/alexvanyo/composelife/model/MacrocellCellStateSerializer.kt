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
import com.alexvanyo.composelife.model.MacroCell.Cell.AliveCell
import com.alexvanyo.composelife.model.MacroCell.Cell.DeadCell
import com.alexvanyo.composelife.model.MacroCell.CellNode
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import kotlin.collections.removeFirst as removeFirstKt

object MacrocellCellStateSerializer : FixedFormatCellStateSerializer {

    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Macrocell

    @Suppress("LongMethod", "CyclomaticComplexMethod", "DestructuringDeclarationWithTooManyEntries", "ReturnCount")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val warnings = mutableListOf<ParameterizedString>()

        var lineIndex = 0

        val iterator = lines.iterator()

        if (!iterator.hasNext()) {
            warnings.add(UnexpectedEmptyFileMessage)

            return DeserializationResult.Successful(
                warnings = warnings,
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.Macrocell,
            )
        }

        val headerLine = iterator.next()
        if (!headerLine.startsWith("[M2]")) {
            return DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedHeaderMessage(headerLine),
                ),
            )
        }
        lineIndex++

        var nodeIndex = 1
        val indexToCellNodeMap = mutableMapOf<Int, CellNode>()

        val nodeRegex = Regex("""(\d+) (\d+) (\d+) (\d+) (\d+)""")

        while (iterator.hasNext()) {
            val line = iterator.next()

            when {
                line.isEmpty() -> {
                    if (iterator.hasNext()) {
                        warnings.add(UnexpectedBlankLineMessage(lineIndex + 1))
                    }
                }
                line.first() == '#' -> {
                    // Comment line, continue
                }
                line.first().isDigit() -> {
                    val result = nodeRegex.matchEntire(line)
                        ?: return DeserializationResult.Unsuccessful(
                            warnings = warnings,
                            errors = listOf(
                                UnexpectedInputMessage(
                                    input = line,
                                    lineIndex = lineIndex,
                                    characterIndex = 0,
                                ),
                            ),
                        )

                    val (_, level, nw, ne, sw, se) = result.groups.toList().map(::checkNotNull)

                    val levelValue = level.value.toInt()
                    val nwValue = nw.value.toInt()
                    val neValue = ne.value.toInt()
                    val swValue = sw.value.toInt()
                    val seValue = se.value.toInt()

                    val node = CellNode(
                        if (nwValue == 0) {
                            createEmptyMacroCell(levelValue - 1)
                        } else {
                            indexToCellNodeMap[nwValue] ?: return DeserializationResult.Unsuccessful(
                                warnings = warnings,
                                errors = listOf(
                                    UnexpectedNodeIdMessage(
                                        lineIndex = lineIndex,
                                        characterIndices = nw.range,
                                    ),
                                ),
                            )
                        },
                        if (neValue == 0) {
                            createEmptyMacroCell(levelValue - 1)
                        } else {
                            indexToCellNodeMap[neValue] ?: return DeserializationResult.Unsuccessful(
                                warnings = warnings,
                                errors = listOf(
                                    UnexpectedNodeIdMessage(
                                        lineIndex = lineIndex,
                                        characterIndices = ne.range,
                                    ),
                                ),
                            )
                        },
                        if (swValue == 0) {
                            createEmptyMacroCell(levelValue - 1)
                        } else {
                            indexToCellNodeMap[swValue] ?: return DeserializationResult.Unsuccessful(
                                warnings = warnings,
                                errors = listOf(
                                    UnexpectedNodeIdMessage(
                                        lineIndex = lineIndex,
                                        characterIndices = sw.range,
                                    ),
                                ),
                            )
                        },
                        if (seValue == 0) {
                            createEmptyMacroCell(levelValue - 1)
                        } else {
                            indexToCellNodeMap[seValue] ?: return DeserializationResult.Unsuccessful(
                                warnings = warnings,
                                errors = listOf(
                                    UnexpectedNodeIdMessage(
                                        lineIndex = lineIndex,
                                        characterIndices = se.range,
                                    ),
                                ),
                            )
                        },
                    )
                    indexToCellNodeMap[nodeIndex++] = node
                }
                else -> {
                    line.forEachIndexed { index, char ->
                        if (char !in setOf('$', '.', '*')) {
                            warnings.add(
                                UnexpectedInputMessage(
                                    input = line,
                                    lineIndex = lineIndex,
                                    characterIndex = index,
                                ),
                            )
                        }
                    }
                    val rows = line.split('$')

                    val node = CellNode(
                        nw = CellNode(
                            nw = CellNode(
                                nw = if (rows.getOrNull(0)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(0)?.getOrNull(1) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(1)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(1)?.getOrNull(1) == '*') AliveCell else DeadCell,
                            ),
                            ne = CellNode(
                                nw = if (rows.getOrNull(0)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(0)?.getOrNull(3) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(1)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(1)?.getOrNull(3) == '*') AliveCell else DeadCell,
                            ),
                            sw = CellNode(
                                nw = if (rows.getOrNull(2)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(2)?.getOrNull(1) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(3)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(3)?.getOrNull(1) == '*') AliveCell else DeadCell,
                            ),
                            se = CellNode(
                                nw = if (rows.getOrNull(2)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(2)?.getOrNull(3) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(3)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(3)?.getOrNull(3) == '*') AliveCell else DeadCell,
                            ),
                        ),
                        ne = CellNode(
                            nw = CellNode(
                                nw = if (rows.getOrNull(0)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(0)?.getOrNull(5) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(1)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(1)?.getOrNull(5) == '*') AliveCell else DeadCell,
                            ),
                            ne = CellNode(
                                nw = if (rows.getOrNull(0)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(0)?.getOrNull(7) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(1)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(1)?.getOrNull(7) == '*') AliveCell else DeadCell,
                            ),
                            sw = CellNode(
                                nw = if (rows.getOrNull(2)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(2)?.getOrNull(5) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(3)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(3)?.getOrNull(5) == '*') AliveCell else DeadCell,
                            ),
                            se = CellNode(
                                nw = if (rows.getOrNull(2)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(2)?.getOrNull(7) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(3)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(3)?.getOrNull(7) == '*') AliveCell else DeadCell,
                            ),
                        ),
                        sw = CellNode(
                            nw = CellNode(
                                nw = if (rows.getOrNull(4)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(4)?.getOrNull(1) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(5)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(5)?.getOrNull(1) == '*') AliveCell else DeadCell,
                            ),
                            ne = CellNode(
                                nw = if (rows.getOrNull(4)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(4)?.getOrNull(3) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(5)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(5)?.getOrNull(3) == '*') AliveCell else DeadCell,
                            ),
                            sw = CellNode(
                                nw = if (rows.getOrNull(6)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(6)?.getOrNull(1) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(7)?.getOrNull(0) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(7)?.getOrNull(1) == '*') AliveCell else DeadCell,
                            ),
                            se = CellNode(
                                nw = if (rows.getOrNull(6)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(6)?.getOrNull(3) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(7)?.getOrNull(2) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(7)?.getOrNull(3) == '*') AliveCell else DeadCell,
                            ),
                        ),
                        se = CellNode(
                            nw = CellNode(
                                nw = if (rows.getOrNull(4)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(4)?.getOrNull(5) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(5)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(5)?.getOrNull(5) == '*') AliveCell else DeadCell,
                            ),
                            ne = CellNode(
                                nw = if (rows.getOrNull(4)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(4)?.getOrNull(7) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(5)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(5)?.getOrNull(7) == '*') AliveCell else DeadCell,
                            ),
                            sw = CellNode(
                                nw = if (rows.getOrNull(6)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(6)?.getOrNull(5) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(7)?.getOrNull(4) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(7)?.getOrNull(5) == '*') AliveCell else DeadCell,
                            ),
                            se = CellNode(
                                nw = if (rows.getOrNull(6)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                ne = if (rows.getOrNull(6)?.getOrNull(7) == '*') AliveCell else DeadCell,
                                sw = if (rows.getOrNull(7)?.getOrNull(6) == '*') AliveCell else DeadCell,
                                se = if (rows.getOrNull(7)?.getOrNull(7) == '*') AliveCell else DeadCell,
                            ),
                        ),
                    )

                    indexToCellNodeMap[nodeIndex++] = node
                }
            }

            lineIndex++
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = HashLifeCellState(
                offset = IntOffset.Zero,
                macroCell = if (nodeIndex == 1) {
                    createEmptyMacroCell(3)
                } else {
                    indexToCellNodeMap.getValue(nodeIndex - 1)
                },
            ),
            format = CellStateFormat.FixedFormat.Macrocell,
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val hashLifeCellState = cellState.toHashLifeCellState()

        return sequence {
            yield("[M2] (ComposeLife 1.0)")
            var nodeIndex = 1

            val cellNodeToIndexMap = mutableMapOf<CellNode, Int>()
            val nodesToEmit = mutableListOf(hashLifeCellState.macroCell as CellNode)

            while (nodesToEmit.isNotEmpty()) {
                val node = nodesToEmit.removeFirstKt()
                node.nw as CellNode
                node.ne as CellNode
                node.sw as CellNode
                node.se as CellNode

                @Suppress("ComplexCondition")
                if (node in cellNodeToIndexMap) {
                    continue
                } else if (node.size == -0) {
                    cellNodeToIndexMap[node] = 0
                } else if (node.level == 3) {
                    yield(
                        (0..7).map { y ->
                            CharArray(8) { x ->
                                if (IntOffset(x, y) in node) '*' else '.'
                            }
                        }
                            .map(::String)
                            .joinToString("$") { it.trimEnd('.') }
                            .trimEnd('$') + '$',
                    )
                    cellNodeToIndexMap[node] = nodeIndex++
                } else if (
                    node.nw in cellNodeToIndexMap &&
                    node.ne in cellNodeToIndexMap &&
                    node.sw in cellNodeToIndexMap &&
                    node.se in cellNodeToIndexMap
                ) {
                    val nwIndex = cellNodeToIndexMap.getValue(node.nw)
                    val neIndex = cellNodeToIndexMap.getValue(node.ne)
                    val swIndex = cellNodeToIndexMap.getValue(node.sw)
                    val seIndex = cellNodeToIndexMap.getValue(node.se)

                    yield("${node.level} $nwIndex $neIndex $swIndex $seIndex")
                    cellNodeToIndexMap[node] = nodeIndex++
                } else {
                    nodesToEmit.add(node.nw)
                    nodesToEmit.add(node.ne)
                    nodesToEmit.add(node.sw)
                    nodesToEmit.add(node.se)
                    nodesToEmit.add(node)
                }
            }
        }
    }
}

private operator fun <T> List<T>.component6(): T = get(5)

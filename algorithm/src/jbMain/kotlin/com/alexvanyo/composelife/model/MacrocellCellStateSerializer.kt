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

import androidx.collection.mutableLongIntMapOf
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.MacroCell.CellNode
import com.alexvanyo.composelife.model.MacroCell.LeafNode
import com.alexvanyo.composelife.model.MacroCell.Level4Node
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
        val indexToLeafNodeMap = mutableMapOf<Int, LeafNode>()
        val indexToMacroCellMap = mutableMapOf<Int, MacroCell>()

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
                    val firstSpaceIndex = line.indexOf(" ")
                    val secondSpaceIndex = line.indexOf(" ", firstSpaceIndex + 1)
                    val thirdSpaceIndex = line.indexOf(" ", secondSpaceIndex + 1)
                    val fourthSpaceIndex = line.indexOf(" ", thirdSpaceIndex + 1)

                    val nwRange = firstSpaceIndex + 1 until secondSpaceIndex // nw.range
                    val neRange = secondSpaceIndex + 1 until thirdSpaceIndex // ne.range
                    val swRange = thirdSpaceIndex + 1 until fourthSpaceIndex // sw.range
                    val seRange = fourthSpaceIndex + 1 until line.length // se.range

                    val node = if (levelValue == 4) {
                        Level4Node(
                            nw = if (nwValue == 0) {
                                0L
                            } else {
                                indexToLeafNodeMap[nwValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = nwRange,
                                        ),
                                    ),
                                )
                            },
                            ne = if (neValue == 0) {
                                0L
                            } else {
                                indexToLeafNodeMap[neValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = neRange,
                                        ),
                                    ),
                                )
                            },
                            sw = if (swValue == 0) {
                                0L
                            } else {
                                indexToLeafNodeMap[swValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = swRange,
                                        ),
                                    ),
                                )
                            },
                            se = if (seValue == 0) {
                                0L
                            } else {
                                indexToLeafNodeMap[seValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = seRange,
                                        ),
                                    ),
                                )
                            },
                        )
                    } else {
                        CellNode(
                            nw = if (nwValue == 0) {
                                createEmptyMacroCell(levelValue - 1)
                            } else {
                                indexToMacroCellMap[nwValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = nwRange,
                                        ),
                                    ),
                                )
                            },
                            ne = if (neValue == 0) {
                                createEmptyMacroCell(levelValue - 1)
                            } else {
                                indexToMacroCellMap[neValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = neRange,
                                        ),
                                    ),
                                )
                            },
                            sw = if (swValue == 0) {
                                createEmptyMacroCell(levelValue - 1)
                            } else {
                                indexToMacroCellMap[swValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = swRange,
                                        ),
                                    ),
                                )
                            },
                            se = if (seValue == 0) {
                                createEmptyMacroCell(levelValue - 1)
                            } else {
                                indexToMacroCellMap[seValue] ?: return DeserializationResult.Unsuccessful(
                                    warnings = warnings,
                                    errors = listOf(
                                        UnexpectedNodeIdMessage(
                                            lineIndex = lineIndex,
                                            characterIndices = seRange,
                                        ),
                                    ),
                                )
                            },
                        )
                    }
                    indexToMacroCellMap[nodeIndex++] = node
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

                    val node =
                        (0..7).sumOf { row ->
                            (0..7).sumOf { column ->
                                if (rows.getOrNull(row)?.getOrNull(column) == '*') {
                                    IntOffset(column, row).toMask()
                                } else {
                                    0L
                                }
                            }
                        }

                    indexToLeafNodeMap[nodeIndex++] = node
                }
            }

            lineIndex++
        }

        return DeserializationResult.Successful(
            warnings = warnings,
            cellState = HashLifeCellState(
                offset = IntOffset.Zero,
                macroCell = if (nodeIndex == 1) {
                    createEmptyMacroCell(4)
                } else {
                    indexToMacroCellMap[nodeIndex - 1] ?: Level4Node(
                        nw = indexToLeafNodeMap.getValue(nodeIndex - 1),
                        ne = 0L,
                        sw = 0L,
                        se = 0L,
                    )
                },
            ),
            format = CellStateFormat.FixedFormat.Macrocell,
        )
    }

    @Suppress("LongMethod", "CyclomaticComplexMethod")
    override fun serializeToString(cellState: CellState): Sequence<String> {
        val hashLifeCellState = cellState.toHashLifeCellState()

        return sequence {
            yield("[M2] (ComposeLife 1.0)")

            var nodeIndex = 1

            val macroCellToIndexMap = mutableMapOf<MacroCell, Int>()
            val leafNodeToIndexMap = mutableLongIntMapOf()
            val nodesToEmit = mutableListOf(hashLifeCellState.macroCell)

            if (hashLifeCellState.macroCell.size == 0) {
                // Fast path: if the cell state is empty, there's nothing to print
                return@sequence
            } else if (hashLifeCellState.macroCell is Level4Node) {
                // Fast path: if the cell state is just a Level4Node, we may be able to print just one leaf node
                val nwIndex = if (hashLifeCellState.macroCell.nw.size == 0) {
                    0
                } else {
                    leafNodeToIndexMap.getOrPut(hashLifeCellState.macroCell.nw) {
                        yieldLeafNode(hashLifeCellState.macroCell.nw)
                        nodeIndex++
                    }
                }
                val neIndex = if (hashLifeCellState.macroCell.ne.size == 0) {
                    0
                } else {
                    leafNodeToIndexMap.getOrPut(hashLifeCellState.macroCell.ne) {
                        yieldLeafNode(hashLifeCellState.macroCell.ne)
                        nodeIndex++
                    }
                }
                val swIndex = if (hashLifeCellState.macroCell.sw.size == 0) {
                    0
                } else {
                    leafNodeToIndexMap.getOrPut(hashLifeCellState.macroCell.sw) {
                        yieldLeafNode(hashLifeCellState.macroCell.sw)
                        nodeIndex++
                    }
                }
                val seIndex = if (hashLifeCellState.macroCell.se.size == 0) {
                    0
                } else {
                    leafNodeToIndexMap.getOrPut(hashLifeCellState.macroCell.se) {
                        yieldLeafNode(hashLifeCellState.macroCell.se)
                        nodeIndex++
                    }
                }
                val nonZeroLeafNodes = listOf(nwIndex, neIndex, swIndex, seIndex).count { it != 0 }
                if (nonZeroLeafNodes != 1) {
                    // If there was only one non-zero leaf node, we don't need to print the Level4Node
                    yield("${hashLifeCellState.macroCell.level} $nwIndex $neIndex $swIndex $seIndex")
                }
                return@sequence
            }

            while (nodesToEmit.isNotEmpty()) {
                val node = nodesToEmit.removeFirstKt()
                @Suppress("ComplexCondition")
                if (node in macroCellToIndexMap) {
                    continue
                } else if (node.size == 0) {
                    macroCellToIndexMap[node] = 0
                } else {
                    when (node) {
                        is Level4Node -> {
                            val nwIndex = if (node.nw.size == 0) {
                                0
                            } else {
                                leafNodeToIndexMap.getOrPut(node.nw) {
                                    yieldLeafNode(node.nw)
                                    nodeIndex++
                                }
                            }
                            val neIndex = if (node.ne.size == 0) {
                                0
                            } else {
                                leafNodeToIndexMap.getOrPut(node.ne) {
                                    yieldLeafNode(node.ne)
                                    nodeIndex++
                                }
                            }
                            val swIndex = if (node.sw.size == 0) {
                                0
                            } else {
                                leafNodeToIndexMap.getOrPut(node.sw) {
                                    yieldLeafNode(node.sw)
                                    nodeIndex++
                                }
                            }
                            val seIndex = if (node.se.size == 0) {
                                0
                            } else {
                                leafNodeToIndexMap.getOrPut(node.se) {
                                    yieldLeafNode(node.se)
                                    nodeIndex++
                                }
                            }
                            yield("${node.level} $nwIndex $neIndex $swIndex $seIndex")
                            macroCellToIndexMap[node] = nodeIndex++
                        }
                        is CellNode -> {
                            if (
                                node.nw in macroCellToIndexMap &&
                                node.ne in macroCellToIndexMap &&
                                node.sw in macroCellToIndexMap &&
                                node.se in macroCellToIndexMap
                            ) {
                                val nwIndex = macroCellToIndexMap.getValue(node.nw)
                                val neIndex = macroCellToIndexMap.getValue(node.ne)
                                val swIndex = macroCellToIndexMap.getValue(node.sw)
                                val seIndex = macroCellToIndexMap.getValue(node.se)

                                yield("${node.level} $nwIndex $neIndex $swIndex $seIndex")
                                macroCellToIndexMap[node] = nodeIndex++
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
        }
    }
}

private suspend fun SequenceScope<String>.yieldLeafNode(leafNode: LeafNode) {
    yield(
        (0..7).map { y ->
            CharArray(8) { x ->
                if (IntOffset(x, y) in leafNode) '*' else '.'
            }
        }
            .map(CharArray::concatToString)
            .joinToString("$") { it.trimEnd('.') }
            .trimEnd('$') + '$',
    )
}

private operator fun <T> List<T>.component6(): T = get(5)

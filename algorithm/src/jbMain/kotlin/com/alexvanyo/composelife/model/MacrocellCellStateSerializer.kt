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

object MacrocellCellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Macrocell

    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val result = f_Algorithm_deserializeMacrocell(lines.toList().toTypedArray())
        val warnings = result.warnings.map { mapMacrocellWarning(it as MacrocellWarning) }

        return when (val status = result.status) {
            is MacrocellStatus.Ok -> DeserializationResult.Successful(
                warnings = warnings,
                cellState = HashLifeCellState(
                    offset = IntOffset.Zero,
                    macroCell = result.macroCell,
                ),
                format = CellStateFormat.FixedFormat.Macrocell,
            )

            is MacrocellStatus.EmptyFile -> DeserializationResult.Successful(
                warnings = listOf(UnexpectedEmptyFileMessage),
                cellState = emptyCellState(),
                format = CellStateFormat.FixedFormat.Macrocell,
            )

            is MacrocellStatus.InvalidHeader -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(UnexpectedHeaderMessage(status.line)),
            )

            is MacrocellStatus.UnexpectedInput -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedInputMessage(
                        input = status.line,
                        lineIndex = status.lineIndex.toInt(),
                        characterIndex = 0,
                    ),
                ),
            )

            is MacrocellStatus.UnexpectedNodeId -> DeserializationResult.Unsuccessful(
                warnings = warnings,
                errors = listOf(
                    UnexpectedNodeIdMessage(
                        lineIndex = status.lineIndex.toInt(),
                        characterIndices = status.rangeStart.toInt()..status.rangeEnd.toInt(),
                    ),
                ),
            )
        }
    }

    private fun mapMacrocellWarning(warning: MacrocellWarning): ParameterizedString = when (warning) {
        is MacrocellWarning.EmptyFile -> UnexpectedEmptyFileMessage

        is MacrocellWarning.BlankLine -> UnexpectedBlankLineMessage(warning.lineIndex.toInt())

        is MacrocellWarning.UnexpectedInput -> UnexpectedInputMessage(
            input = warning.input,
            lineIndex = warning.lineIndex.toInt(),
            characterIndex = warning.columnIndex.toInt(),
        )
    }

    override fun serializeToString(cellState: CellState): Sequence<String> {
        val root = cellState.toHashLifeCellState().macroCell
        f_Algorithm_macrocellSingleLeaf(root)?.let { leaf ->
            return sequenceOf(f_Algorithm_macrocellHeader(), f_Algorithm_formatLeafNode(leaf))
        }
        val writer = MacrocellWriter()
        writer.addTree(root)
        return writer.lines.asSequence()
    }
}

/**
 * Writes the lines of `serializeMacrocell` in Lean, which models this with `MacrocellWriterState.addTree`.
 *
 * Nodes are numbered by line. Leaves are memoized by value and nodes by the numbers of their children, so equal
 * subtrees are written once. Subtrees are also memoized by identity, so a shared subtree is walked once:
 * structural equality of [MacroCell] does not short-circuit on shared children, so comparing two equal but
 * separately built subtrees would walk every path through them.
 */
private class MacrocellWriter {
    val lines = mutableListOf(f_Algorithm_macrocellHeader())

    private val leafIds = mutableMapOf<ULong, UInt>()

    private val nodeIds = mutableMapOf<NodeKey, UInt>()

    private val treeIds = mutableMapOf<IdentityKey, UInt>()

    private data class NodeKey(val level: UInt, val nw: UInt, val ne: UInt, val sw: UInt, val se: UInt)

    private class IdentityKey(val node: MacroCell) {
        override fun equals(other: Any?): Boolean = other is IdentityKey && other.node === node

        override fun hashCode(): Int = node.hashCode()
    }

    private fun nextId(): UInt = lines.size.toUInt()

    private fun addLeaf(leaf: ULong): UInt = if (leaf == 0uL) {
        0u
    } else {
        leafIds.getOrPut(leaf) {
            val id = nextId()
            lines.add(f_Algorithm_formatLeafNode(leaf))
            id
        }
    }

    private fun addNode(level: UInt, nw: UInt, ne: UInt, sw: UInt, se: UInt): UInt =
        nodeIds.getOrPut(NodeKey(level, nw, ne, sw, se)) {
            val id = nextId()
            lines.add(f_Algorithm_formatMacrocellNode(level, nw, ne, sw, se))
            id
        }

    /**
     * Returns the number of [node], or 0 if it is empty. Emptiness is read from the children, not from
     * [MacroCell.size], which wraps for nodes of 2^64 or more alive cells.
     */
    fun addTree(node: MacroCell): UInt {
        // Not getOrPut: the children are added first, which adds to treeIds.
        val key = IdentityKey(node)
        return treeIds[key] ?: addNewTree(node).also { treeIds[key] = it }
    }

    private fun addNewTree(node: MacroCell): UInt = when (node) {
        is MacroCell.Level4Node -> if ((node.nw or node.ne or node.sw or node.se) == 0uL) {
            0u
        } else {
            val nw = addLeaf(node.nw)
            val ne = addLeaf(node.ne)
            val sw = addLeaf(node.sw)
            val se = addLeaf(node.se)
            addNode(4u, nw, ne, sw, se)
        }

        is MacroCell.CellNode -> {
            val nw = addTree(node.nw)
            val ne = addTree(node.ne)
            val sw = addTree(node.sw)
            val se = addTree(node.se)
            if ((nw or ne or sw or se) == 0u) 0u else addNode(node.level(), nw, ne, sw, se)
        }
    }
}

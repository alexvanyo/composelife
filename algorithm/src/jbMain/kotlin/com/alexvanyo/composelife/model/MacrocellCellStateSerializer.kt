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

@OptIn(ExperimentalUnsignedTypes::class)
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
        val dag = MacrocellDag()
        dag.add(cellState.toHashLifeCellState().macroCell)
        return f_Algorithm_serializeMacrocellDag(dag.entries(), dag.kids()).asSequence().map { it as String }
    }
}

/**
 * The distinct subtrees of a tree, children first and the tree last, for `serializeMacrocellDag` in Lean, which
 * numbers and writes them (see `macrocell_dag_round_trip`).
 *
 * Subtrees are collected by identity, so a shared subtree is one entry and is walked once: structural equality of
 * [MacroCell] does not short-circuit on shared children, so comparing two equal but separately built subtrees would
 * walk every path through them. Equal subtrees that are not shared are merged by Lean, which memoizes leaves by value
 * and nodes by the numbers of their children.
 */
@OptIn(ExperimentalUnsignedTypes::class)
private class MacrocellDag {
    private val entries = mutableListOf<MacroCell>()

    private var kids = UIntArray(INITIAL_KIDS)

    private val entryIds = mutableMapOf<IdentityKey, UInt>()

    private class IdentityKey(val node: MacroCell) {
        override fun equals(other: Any?): Boolean = other is IdentityKey && other.node === node

        override fun hashCode(): Int = node.hashCode()
    }

    /**
     * Returns the entry number of [node], adding it and its subtrees if they are new.
     */
    fun add(node: MacroCell): UInt {
        // Not getOrPut: the children are added first, which adds to entryIds.
        val key = IdentityKey(node)
        return entryIds[key] ?: addNew(node).also { entryIds[key] = it }
    }

    private fun addNew(node: MacroCell): UInt {
        val children = when (node) {
            is MacroCell.Level4Node -> uintArrayOf(0u, 0u, 0u, 0u)
            is MacroCell.CellNode -> uintArrayOf(add(node.nw), add(node.ne), add(node.sw), add(node.se))
        }
        val id = entries.size
        entries.add(node)
        if (kids.size < KIDS_PER_ENTRY * entries.size) {
            kids = kids.copyOf(2 * kids.size)
        }
        children.copyInto(kids, KIDS_PER_ENTRY * id)
        return id.toUInt()
    }

    fun entries(): Array<Any?> = Array(entries.size) { entries[it] }

    fun kids(): UIntArray = kids.copyOf(KIDS_PER_ENTRY * entries.size)

    private companion object {
        const val KIDS_PER_ENTRY = 4
        const val INITIAL_KIDS = 64
    }
}

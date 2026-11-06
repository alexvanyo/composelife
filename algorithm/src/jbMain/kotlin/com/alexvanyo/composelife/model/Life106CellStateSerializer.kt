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

object Life106CellStateSerializer : FixedFormatCellStateSerializer {
    override val format: CellStateFormat.FixedFormat = CellStateFormat.FixedFormat.Life106

    @Suppress("UNCHECKED_CAST")
    override fun deserializeToCellState(lines: Sequence<String>): DeserializationResult {
        val linesArray = lines.toList().toTypedArray()
        val result = f_Algorithm_deserializeLife106(linesArray as Array<Any?>)

        return when (result.status) {
            0u -> {
                val aliveCells = result.cells.map {
                    val pair = it as Pair<*, *>
                    val x = if (pair.first is UInt) (pair.first as UInt).toInt() else (pair.first as Int)
                    val y = if (pair.second is UInt) (pair.second as UInt).toInt() else (pair.second as Int)
                    IntOffset(x, y)
                }.toSet()
                DeserializationResult.Successful(
                    warnings = emptyList(),
                    cellState = CellState(aliveCells),
                    format = CellStateFormat.FixedFormat.Life106,
                )
            }

            1u -> {
                DeserializationResult.Successful(
                    warnings = listOf(UnexpectedEmptyFileMessage),
                    cellState = emptyCellState(),
                    format = CellStateFormat.FixedFormat.Life106,
                )
            }

            2u -> {
                DeserializationResult.Unsuccessful(
                    warnings = emptyList(),
                    errors = listOf(
                        UnexpectedHeaderMessage(result.errLineContent),
                    ),
                )
            }

            else -> {
                DeserializationResult.Unsuccessful(
                    warnings = emptyList(),
                    errors = listOf(
                        UnexpectedInputMessage(result.errLineContent, result.errLineIndex.toInt(), 0),
                    ),
                )
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun serializeToString(cellState: CellState): Sequence<String> {
        val cells = cellState.aliveCells.map { Pair(it.x.toUInt(), it.y.toUInt()) }.toTypedArray()
        val lines = f_Algorithm_serializeLife106(cells as Array<Any?>)
        return lines.asSequence().map { it as String }
    }
}

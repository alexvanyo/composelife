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

import androidx.compose.runtime.Immutable
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import com.alexvanyo.composelife.geometry.toIntOffset
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerializationException
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/**
 * The cell state for a single generation.
 */
@Serializable(with = JsonCellStateSerialization::class)
@Immutable
abstract class CellState {
    /**
     * The set of all cells alive at this generation.
     */
    abstract val aliveCells: Set<IntOffset>

    /**
     * Returns a new cell state, where a cell is alive in the new cell state if it is alive in
     * this cell state, or in the [other] cell state (OR).
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun union(other: CellState) = CellState(aliveCells.union(other.aliveCells))

    /**
     * Returns a new cell state with offset by the given [offset].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun offsetBy(offset: IntOffset) = CellState(aliveCells.map { it + offset }.toSet())

    /**
     * Returns a new cell state where the cell at the given [offset] is set to be alive or dead as
     * specified by [isAlive].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun withCell(offset: IntOffset, isAlive: Boolean): CellState =
        if (isAlive) {
            CellState(aliveCells + offset)
        } else {
            CellState(aliveCells - offset)
        }

    /**
     * Returns the list of alive cells that are contained within the given [cellWindow].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun getAliveCellsInWindow(cellWindow: CellWindow): Iterable<IntOffset> =
        cellWindow.containedPoints().filter { it in aliveCells }

    /**
     * Returns the [CellWindow] describing the minimal bounding box required to enclose all alive cells
     * in this cell state. If the cell state is empty, this will return a [CellWindow] of [IntRect.Zero].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open val boundingBox: CellWindow get() =
        CellWindow(
            if (aliveCells.isEmpty()) {
                IntRect.Zero
            } else {
                IntRect(
                    left = aliveCells.minOf { it.x },
                    top = aliveCells.minOf { it.y },
                    right = aliveCells.maxOf { it.x } + 1,
                    bottom = aliveCells.maxOf { it.y } + 1,
                )
            },
        )

    override fun equals(other: Any?): Boolean =
        if (other !is CellState) {
            false
        } else {
            aliveCells.size == other.aliveCells.size &&
                aliveCells.containsAll(other.aliveCells)
        }

    override fun hashCode(): Int = aliveCells.toSet().hashCode()
}

/**
 * Returns `true` if this [CellState] and the [other] [CellState] are equivalent with the possible exception of being
 * offset differently (in other words, different only by translation).
 *
 * This does not attempt to check equivalence against rotation or reflection.
 */
fun CellState.equalsModuloOffset(other: CellState): Boolean =
    if (aliveCells.size != other.aliveCells.size) {
        false
    } else if (aliveCells.isEmpty()) {
        true
    } else {
        val topLeftOffset = IntOffset(aliveCells.minOf(IntOffset::x), aliveCells.minOf(IntOffset::y))
        val otherTopLeftOffset = IntOffset(other.aliveCells.minOf(IntOffset::x), other.aliveCells.minOf(IntOffset::y))
        offsetBy(otherTopLeftOffset - topLeftOffset) == other
    }

fun CellState(aliveCells: Set<IntOffset>): CellState = CellStateImpl(aliveCells)

fun emptyCellState(): CellState = CellState(emptySet())

fun Set<Pair<Int, Int>>.toCellState(): CellState = CellState(map(Pair<Int, Int>::toIntOffset).toSet())

object JsonCellStateSerialization : KSerializer<CellState> by
FixedFormatKSerializer(RunLengthEncodedCellStateSerializer)

class FixedFormatKSerializer(
    private val fixedFormatCellStateSerializer: FixedFormatCellStateSerializer,
) : KSerializer<CellState> {
    private val delegateSerializer = ListSerializer(String.serializer())

    @OptIn(ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor = SerialDescriptor(
        "com.alexvanyo.composelife.model.CellState.${fixedFormatCellStateSerializer.format._name}",
        delegateSerializer.descriptor,
    )

    override fun deserialize(decoder: Decoder): CellState {
        val lines = delegateSerializer.deserialize(decoder)
        val deserializationResult = fixedFormatCellStateSerializer.deserializeToCellState(
            lines.asSequence(),
        )
        return when (deserializationResult) {
            is DeserializationResult.Successful -> {
                if (deserializationResult.warnings.isNotEmpty()) {
                    throw SerializationException(
                        "Warnings when parsing cell state!\n" + deserializationResult.warnings.joinToString("\n"),
                    )
                }
                deserializationResult.cellState
            }

            is DeserializationResult.Unsuccessful -> {
                throw SerializationException(
                    "Warnings when parsing cell state!\n" + deserializationResult.warnings.joinToString("\n"),
                )
            }
        }
    }

    override fun serialize(encoder: Encoder, value: CellState) {
        val lines = fixedFormatCellStateSerializer.serializeToString(value).toList()
        delegateSerializer.serialize(encoder, lines)
    }
}

/**
 * A simple implementation of [CellState] backed by a normal [Set].
 */
private class CellStateImpl(
    override val aliveCells: Set<IntOffset>,
) : CellState() {
    override fun toString(): String = "CellStateImpl(${aliveCells.toSet()})"
}

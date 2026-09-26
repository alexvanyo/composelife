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
@file:Suppress("TooManyFunctions", "NOTHING_TO_INLINE")

package com.alexvanyo.composelife.model

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.MacroCell.CellNode
import com.alexvanyo.composelife.model.MacroCell.LeafNode
import com.alexvanyo.composelife.model.MacroCell.Level4Node

internal inline fun createLeafNode(cellState: CellState, offset: IntOffset): LeafNode {
    var result = 0L
    for (i in 0..63) {
        val inAliveCells = if ((offset + intOffsetFromBit(i)) in cellState.aliveCells) 1L else 0L
        result = result or (inAliveCells shl i)
    }
    return result
}

/**
 * Creates a [MacroCell] with the given [level] as a window looking into [CellState] at [offset].
 */
internal fun createMacroCell(cellState: CellState, offset: IntOffset, @IntRange(from = 4) level: Int): MacroCell {
    val offsetDiff = 1 shl (level - 1)
    return if (level == 4) {
        Level4Node(
            nw = createLeafNode(cellState, offset),
            ne = createLeafNode(cellState, offset + IntOffset(offsetDiff, 0)),
            sw = createLeafNode(cellState, offset + IntOffset(0, offsetDiff)),
            se = createLeafNode(cellState, offset + IntOffset(offsetDiff, offsetDiff)),
        )
    } else {
        CellNode(
            nw = createMacroCell(cellState, offset, level - 1),
            ne = createMacroCell(cellState, offset + IntOffset(offsetDiff, 0), level - 1),
            sw = createMacroCell(cellState, offset + IntOffset(0, offsetDiff), level - 1),
            se = createMacroCell(cellState, offset + IntOffset(offsetDiff, offsetDiff), level - 1),
        )
    }
}

internal suspend inline fun SequenceScope<IntOffset>.yieldLeafNode(
    leafNode: LeafNode,
    offset: IntOffset,
    cellWindow: CellWindow,
) {
    for (i in 0..63) {
        if ((leafNode and (1L shl i)) != 0L) {
            val intOffsetFromBit = intOffsetFromBit(i)
            if (intOffsetFromBit.x in cellWindow.left until cellWindow.right &&
                intOffsetFromBit.y in cellWindow.top until cellWindow.bottom
            ) {
                yield(offset + intOffsetFromBit)
            }
        }
    }
}

/**
 * Returns an [Iterator] of [IntOffset] for every alive cell within the [cellWindow] represented by this [MacroCell],
 * with the given upper left corner [offset].
 */
internal fun MacroCell.iterator(offset: IntOffset, cellWindow: CellWindow): Iterator<IntOffset> {
    val macroCell = this
    val offsetDiff = 1 shl (level - 1)
    return iterator {
        @Suppress("ComplexCondition")
        if (
            size > 0 &&
            cellWindow.right >= 1 &&
            cellWindow.bottom >= 1 &&
            cellWindow.left < 1 shl level &&
            cellWindow.top < 1 shl level
        ) {
            when (macroCell) {
                is Level4Node -> {
                    yieldLeafNode(nw, offset, cellWindow)
                    yieldLeafNode(
                        ne,
                        offset + IntOffset(offsetDiff, 0),
                        cellWindow.translate(IntOffset(-offsetDiff, 0)),
                    )
                    yieldLeafNode(
                        sw,
                        offset + IntOffset(0, offsetDiff),
                        cellWindow.translate(IntOffset(0, -offsetDiff)),
                    )
                    yieldLeafNode(
                        se,
                        offset + IntOffset(offsetDiff, offsetDiff),
                        cellWindow.translate(IntOffset(-offsetDiff, -offsetDiff)),
                    )
                }

                is CellNode -> {
                    yieldAll(macroCell.nw.iterator(offset, cellWindow))
                    yieldAll(
                        macroCell.ne.iterator(
                            offset + IntOffset(offsetDiff, 0),
                            cellWindow.translate(IntOffset(-offsetDiff, 0)),
                        ),
                    )
                    yieldAll(
                        macroCell.sw.iterator(
                            offset + IntOffset(0, offsetDiff),
                            cellWindow.translate(IntOffset(0, -offsetDiff)),
                        ),
                    )
                    yieldAll(
                        macroCell.se.iterator(
                            offset + IntOffset(offsetDiff, offsetDiff),
                            cellWindow.translate(IntOffset(-offsetDiff, -offsetDiff)),
                        ),
                    )
                }
            }
        }
    }
}

private inline fun LeafNode.containsAll(targets: Collection<IntOffset>): Boolean {
    for (target in targets) {
        if ((this and target.toMask()) == 0L) {
            return false
        }
    }
    return true
}

/**
 * An optimized version of [contains] for a collection of [targets].
 *
 * This runs in O(targets.size * level) time.
 */
@Suppress("ReturnCount")
internal fun MacroCell.containsAll(targets: Collection<IntOffset>): Boolean {
    // Fast path: vacuously true
    if (targets.isEmpty()) return true

    // Fast path: if our size is less than the total number of targets, we can't possibly contain all
    if (size < targets.size) return false

    // Invariant: if size was zero, but size < targets.size, then targets.size == 0, so we also should have returned
    check(size > 0)

    // We can't contain targets outside of the representation
    if (targets.any { target -> target.x !in 0 until (1 shl level) || target.y !in 0 until (1 shl level) }) {
        return false
    }

    val offsetDiff = 1 shl (level - 1)

    val (northTargets, southTargets) =
        targets.partition { target ->
            target.y < offsetDiff
        }
    val (northWestTargets, northEastTargets) =
        northTargets.partition { target ->
            target.x < offsetDiff
        }
    val (southWestTargets, southEastTargets) =
        southTargets.partition { target ->
            target.x < offsetDiff
        }

    // Recurse on subtrees
    return when (this) {
        is Level4Node -> {
            nw.containsAll(northWestTargets) &&
                ne.containsAll(northEastTargets.map { it + IntOffset(-offsetDiff, 0) }) &&
                sw.containsAll(southWestTargets.map { it + IntOffset(0, -offsetDiff) }) &&
                se.containsAll(southEastTargets.map { it + IntOffset(-offsetDiff, -offsetDiff) })
        }

        is CellNode -> {
            nw.containsAll(northWestTargets) &&
                ne.containsAll(northEastTargets.map { it + IntOffset(-offsetDiff, 0) }) &&
                sw.containsAll(southWestTargets.map { it + IntOffset(0, -offsetDiff) }) &&
                se.containsAll(southEastTargets.map { it + IntOffset(-offsetDiff, -offsetDiff) })
        }
    }
}

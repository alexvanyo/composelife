/*
 * Copyright 2026 The Android Open Source Project
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
@file:OptIn(ExperimentalUnsignedTypes::class)

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.algorithm.FlatHashLifeArena
import com.alexvanyo.composelife.algorithm.FlatHashLifeArenaException

internal const val UNCOMPUTED_ID: UInt = 0xFFFFFFFFu

internal fun createFlatArena(capacityPow2: Int, maxCapacityPow2: Int = 18): FlatHashLifeArena {
    val cap = 1 shl capacityPow2
    val mask = (cap - 1).toUInt()
    val arena = FlatHashLifeArena(
        l4Nw = ULongArray(cap),
        l4Ne = ULongArray(cap),
        l4Sw = ULongArray(cap),
        l4Se = ULongArray(cap),
        l4StepRes = ULongArray(cap),
        l4HasRes = UByteArray(cap),
        l4Buckets = UIntArray(cap) { UNCOMPUTED_ID },
        l4Next = UIntArray(cap) { UNCOMPUTED_ID },
        l4Count = 0u,
        l4Mask = mask,
        cellNw = UIntArray(cap),
        cellNe = UIntArray(cap),
        cellSw = UIntArray(cap),
        cellSe = UIntArray(cap),
        cellLevel = UByteArray(cap),
        cellPop = ULongArray(cap),
        cellStepRes = UIntArray(cap) { UNCOMPUTED_ID },
        cellBuckets = UIntArray(cap) { UNCOMPUTED_ID },
        cellNext = UIntArray(cap) { UNCOMPUTED_ID },
        cellCount = 0u,
        cellMask = mask,
        remapL4 = UIntArray(maxOf(128, (1 shl maxCapacityPow2) + 128)),
        remapCell = UIntArray((1 shl maxCapacityPow2) + 256),
        overflow = 0u,
    )
    arena.initEmptyNodes()
    return arena
}

private fun createLevel4Tiles(
    cellState: CellState,
    arena: FlatHashLifeArena,
    minX: Int,
    minY: Int,
): Map<IntOffset, UInt>? {
    val tileGroups = cellState.aliveCells.groupBy {
        IntOffset((it.x - minX).floorDiv(16), (it.y - minY).floorDiv(16))
    }
    val currentCoords = mutableMapOf<IntOffset, UInt>()
    for ((tileCoord, _) in tileGroups) {
        val tileOrigin = IntOffset(minX + tileCoord.x * 16, minY + tileCoord.y * 16)
        val nw = createLeafNode(cellState, tileOrigin)
        val ne = createLeafNode(cellState, tileOrigin + IntOffset(8, 0))
        val sw = createLeafNode(cellState, tileOrigin + IntOffset(0, 8))
        val se = createLeafNode(cellState, tileOrigin + IntOffset(8, 8))
        val l4Id = arena.internLevel4(nw, ne, sw, se)
        if (arena.overflow != 0u.toUByte() || l4Id == UNCOMPUTED_ID) return null
        currentCoords[tileCoord] = l4Id
    }
    return currentCoords
}

private fun buildQuadtreeLevels(initialCoords: Map<IntOffset, UInt>, arena: FlatHashLifeArena): UInt? {
    var currentCoords = initialCoords
    var currentLevel = 4
    while (currentCoords.size > 1 || currentLevel < 5) {
        val nextLevel = currentLevel + 1
        val emptyChild = if (currentLevel <= 4) 0u else (currentLevel - 5).toUInt()
        val nextCoords = mutableMapOf<IntOffset, UInt>()
        val processedParents = mutableSetOf<IntOffset>()
        for (coord in currentCoords.keys) {
            val parent = IntOffset(coord.x shr 1, coord.y shr 1)
            if (!processedParents.add(parent)) continue

            val nw = currentCoords[IntOffset(parent.x * 2, parent.y * 2)] ?: emptyChild
            val ne = currentCoords[IntOffset(parent.x * 2 + 1, parent.y * 2)] ?: emptyChild
            val sw = currentCoords[IntOffset(parent.x * 2, parent.y * 2 + 1)] ?: emptyChild
            val se = currentCoords[IntOffset(parent.x * 2 + 1, parent.y * 2 + 1)] ?: emptyChild

            val cellId = arena.internCellNode(nextLevel.toUByte(), nw, ne, sw, se)
            if (arena.overflow != 0u.toUByte() || cellId == UNCOMPUTED_ID) return null
            nextCoords[parent] = cellId
        }
        currentCoords = nextCoords
        currentLevel = nextLevel
    }
    return currentCoords.values.single()
}

internal fun buildQuadtreeBottomUp(cellState: CellState, arena: FlatHashLifeArena): Pair<IntOffset, UInt>? =
    if (cellState.aliveCells.isEmpty()) {
        IntOffset.Zero to 0u
    } else {
        var minX = Int.MAX_VALUE
        var minY = Int.MAX_VALUE
        for (cell in cellState.aliveCells) {
            minX = minOf(minX, cell.x)
            minY = minOf(minY, cell.y)
        }
        val initialCoords = createLevel4Tiles(cellState, arena, minX, minY)
        val rootId = initialCoords?.let { buildQuadtreeLevels(it, arena) }
        rootId?.let { IntOffset(minX, minY) to it }
    }

/**
 * Imports a [HashLifeCellState] into [arena] using a DAG-based bottom-up traversal with subtree memoization.
 *
 * This avoids exponential tree traversal costs on highly repetitive patterns where identical subtrees
 * are shared across quadrants. A level 4 root is imported as its centered level 6 expansion.
 *
 * Returns `null` if [arena] runs out of capacity.
 */
@Suppress("CyclomaticComplexMethod")
internal fun internMacroCellDag(cellState: HashLifeCellState, arena: FlatHashLifeArena): Pair<IntOffset, UInt>? {
    val root = cellState.macroCell
    if (root is MacroCell.Level4Node) {
        val (x, yAndRootId) =
            arena.importLevel4Root(cellState.offset.x, cellState.offset.y, root.nw, root.ne, root.sw, root.se)
        val (y, rootId) = yAndRootId
        return when {
            rootId != UNCOMPUTED_ID -> IntOffset(x, y) to rootId

            arena.overflow != 0u.toUByte() -> null

            else -> throw FlatHashLifeArenaException(
                "Expanded pattern exceeds the coordinate range of FlatHashLifeArena",
            )
        }
    }

    val memo = mutableMapOf<MacroCell, UInt>()

    fun internLevel4(node: MacroCell.Level4Node): UInt {
        val l4Id = arena.internLevel4(node.nw, node.ne, node.sw, node.se)
        return if (arena.overflow != 0u.toUByte()) UNCOMPUTED_ID else l4Id
    }

    fun intern(node: MacroCell): UInt {
        memo[node]?.let { return it }
        val id = when (node) {
            is MacroCell.Level4Node -> internLevel4(node)

            is MacroCell.CellNode -> {
                val lvl = node.level()
                if (node.size() == 0uL && lvl in 5u..60u) {
                    lvl - 5u
                } else {
                    val nwId = intern(node.nw)
                    val neId = intern(node.ne)
                    val swId = intern(node.sw)
                    val seId = intern(node.se)
                    val anyUncomputed = nwId == UNCOMPUTED_ID || neId == UNCOMPUTED_ID
                    if (anyUncomputed || swId == UNCOMPUTED_ID || seId == UNCOMPUTED_ID) {
                        UNCOMPUTED_ID
                    } else {
                        val cellId = arena.internCellNode(lvl.toUByte(), nwId, neId, swId, seId)
                        if (arena.overflow != 0u.toUByte()) UNCOMPUTED_ID else cellId
                    }
                }
            }
        }
        memo[node] = id
        return id
    }

    val rootId = intern(root)
    return if (arena.overflow != 0u.toUByte() || rootId == UNCOMPUTED_ID) null else cellState.offset to rootId
}

/**
 * A [CellState] backed directly by the append-only structural arrays of a [FlatHashLifeArena] epoch.
 *
 * Within an arena epoch, every structural slot is write-once within an arena and never mutated after creation.
 * This allows $O(1)$ zero-copy snapshot creation per generation and $O(1)$ root handoff on consecutive steps,
 * while allowing the UI thread to traverse the quadtree lock-free without allocating `MacroCell` objects.
 */
internal class FlatHashLifeCellState(val offset: IntOffset, val rootNodeId: UInt, val arena: FlatHashLifeArena) :
    CellState() {

    private val l4Nw = arena.l4Nw
    private val l4Ne = arena.l4Ne
    private val l4Sw = arena.l4Sw
    private val l4Se = arena.l4Se
    private val cellNw = arena.cellNw
    private val cellNe = arena.cellNe
    private val cellSw = arena.cellSw
    private val cellSe = arena.cellSe
    private val cellLevel = arena.cellLevel
    private val cellPop = arena.cellPop

    val rootLevel: Int = cellLevel[rootNodeId.toInt()].toInt()

    override val aliveCells: Set<IntOffset> =
        object : Set<IntOffset> {
            override val size: Int = cellPop[rootNodeId.toInt()].toInt()

            override fun contains(element: IntOffset): Boolean = containsOffset(element)

            override fun containsAll(elements: Collection<IntOffset>): Boolean =
                elements.isEmpty() || (size >= elements.size && elements.all(::containsOffset))

            override fun isEmpty(): Boolean = size == 0

            override fun iterator(): Iterator<IntOffset> {
                val windowSize = if (rootLevel >= 30) Int.MAX_VALUE else (1 shl rootLevel)
                return windowIterator(
                    CellWindow(
                        IntRect(
                            IntOffset.Zero,
                            IntSize(windowSize, windowSize),
                        ),
                    ),
                )
            }
        }

    private fun containsOffset(element: IntOffset): Boolean = arena.containsCell(
        rootNodeId,
        element.x.toLong() - offset.x.toLong(),
        element.y.toLong() - offset.y.toLong(),
    )

    private fun isWindowOutside(window: CellWindow, span: Int): Boolean = window.right < 1 || window.bottom < 1 ||
        (span != Int.MAX_VALUE && (window.left >= span || window.top >= span))

    private suspend fun SequenceScope<IntOffset>.yieldLevel4(l4Id: Int, nodeOffset: IntOffset, window: CellWindow) {
        if (l4Id == 0 || isWindowOutside(window, 16)) {
            return
        }
        val nw = l4Nw[l4Id]
        if (nw != 0uL) {
            yieldLeafNode(nw, nodeOffset, window)
        }
        val ne = l4Ne[l4Id]
        if (ne != 0uL) {
            yieldLeafNode(
                ne,
                nodeOffset + IntOffset(8, 0),
                window.translate(IntOffset(-8, 0)),
            )
        }
        val sw = l4Sw[l4Id]
        if (sw != 0uL) {
            yieldLeafNode(
                sw,
                nodeOffset + IntOffset(0, 8),
                window.translate(IntOffset(0, -8)),
            )
        }
        val se = l4Se[l4Id]
        if (se != 0uL) {
            yieldLeafNode(
                se,
                nodeOffset + IntOffset(8, 8),
                window.translate(IntOffset(-8, -8)),
            )
        }
    }

    private suspend fun SequenceScope<IntOffset>.yieldCell(
        id: Int,
        level: Int,
        nodeOffset: IntOffset,
        window: CellWindow,
    ) {
        val span = if (level >= 30) Int.MAX_VALUE else (1 shl level)
        if (cellPop[id] == 0uL || isWindowOutside(window, span)) {
            return
        }
        val half = if (level >= 31) 1 shl 30 else (1 shl (level - 1))
        val nwId = cellNw[id].toInt()
        val neId = cellNe[id].toInt()
        val swId = cellSw[id].toInt()
        val seId = cellSe[id].toInt()
        if (level == 5) {
            yieldLevel4(nwId, nodeOffset, window)
            yieldLevel4(
                neId,
                nodeOffset + IntOffset(half, 0),
                window.translate(IntOffset(-half, 0)),
            )
            yieldLevel4(
                swId,
                nodeOffset + IntOffset(0, half),
                window.translate(IntOffset(0, -half)),
            )
            yieldLevel4(
                seId,
                nodeOffset + IntOffset(half, half),
                window.translate(IntOffset(-half, -half)),
            )
        } else {
            val childLvl = level - 1
            yieldCell(nwId, childLvl, nodeOffset, window)
            yieldCell(
                neId,
                childLvl,
                nodeOffset + IntOffset(half, 0),
                window.translate(IntOffset(-half, 0)),
            )
            yieldCell(
                swId,
                childLvl,
                nodeOffset + IntOffset(0, half),
                window.translate(IntOffset(0, -half)),
            )
            yieldCell(
                seId,
                childLvl,
                nodeOffset + IntOffset(half, half),
                window.translate(IntOffset(-half, -half)),
            )
        }
    }

    private fun windowIterator(window: CellWindow): Iterator<IntOffset> = iterator {
        yieldCell(rootNodeId.toInt(), rootLevel, offset, window)
    }

    override fun offsetBy(offset: IntOffset): CellState = FlatHashLifeCellState(
        offset = this.offset + offset,
        rootNodeId = rootNodeId,
        arena = arena,
    )

    override fun withCell(offset: IntOffset, isAlive: Boolean): CellState = if (containsOffset(offset) == isAlive) {
        this
    } else {
        toHashLifeCellState().withCell(offset, isAlive)
    }

    override fun getAliveCellsInWindow(cellWindow: CellWindow): Iterable<IntOffset> =
        Iterable { windowIterator(cellWindow.translate(-offset)) }

    override fun toString(): String = "FlatHashLifeCellState(${aliveCells.toSet()})"
}

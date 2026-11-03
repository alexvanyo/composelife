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
import com.alexvanyo.composelife.algorithm.FlatHashLifeArena
import com.alexvanyo.composelife.algorithm.FlatHashLifeArenaException
import com.alexvanyo.composelife.algorithm.f_Algorithm_cellCursorDone
import com.alexvanyo.composelife.algorithm.f_Algorithm_cellsToMacroCell
import com.alexvanyo.composelife.algorithm.f_Algorithm_importNeedsChildren
import com.alexvanyo.composelife.algorithm.f_Algorithm_leafChunkKey

internal const val UNCOMPUTED_ID: UInt = 0xFFFFFFFFu

internal fun createFlatArena(capacityPow2: Int): FlatHashLifeArena {
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
        // Room to copy from any arena of at most this capacity; `ensureScratchFor` grows them for larger sources.
        remapL4 = UIntArray(maxOf(MIN_REMAP_L4_SIZE, cap)),
        remapCell = UIntArray(cap + COPY_STACK_DEPTH),
        overflow = 0u,
    )
    arena.initEmptyNodes()
    return arena
}

/**
 * Grows the scratch tables of this arena, if needed, so that it can copy any subgraph of [src]
 * (`canCopySubgraphFrom`). Replacing the scratch tables is `withScratch` in Lean, which keeps the arena well-formed
 * with the same nodes and states (`flat_withScratch_correct`).
 */
internal fun FlatHashLifeArena.ensureScratchFor(src: FlatHashLifeArena) {
    val l4Size = maxOf(MIN_REMAP_L4_SIZE, src.l4Count.toInt())
    if (remapL4.size < l4Size) {
        remapL4 = UIntArray(l4Size)
    }
    val cellSize = src.cellCount.toInt() + COPY_STACK_DEPTH
    if (remapCell.size < cellSize) {
        remapCell = UIntArray(cellSize)
    }
}

/**
 * The smallest `remapL4`: the step work stack needs 26 frames of 5 entries
 * (`flat_stepOneGeneration_fails_only_when_full`).
 */
private const val MIN_REMAP_L4_SIZE = 256

/** The copy work stack that `remapCell` holds after its remap entries (`copyStackDepth` in Lean). */
private const val COPY_STACK_DEPTH = 256

/**
 * The key of a cell, as `cellKeyOf` in Lean computes it: `x + 2^31` in the high 32 bits and `y + 2^31` in the low
 * 32 bits.
 */
private fun cellKeyOf(cell: IntOffset): ULong =
    ((cell.x.toLong() + KEY_BIAS).toULong() shl 32) or (cell.y.toLong() + KEY_BIAS).toULong()

/**
 * The coordinate of 32 bits of a key (`keyCoord` in Lean).
 */
private fun keyCoordinate(bits: ULong): Int = (bits.toLong() - KEY_BIAS).toInt()

/**
 * The cell of a key (`keyCoord` in Lean).
 */
private fun keyCell(key: ULong): IntOffset = IntOffset(keyCoordinate(key shr 32), keyCoordinate(key and 0xFFFFFFFFuL))

private const val KEY_BIAS = 2147483648L

/**
 * Imports the alive cells of any [CellState] into [arena]: `cellsToMacroCell` (verified in Lean) builds their quadtree
 * at the corner of their bounding box, which is then imported with [internMacroCellDag].
 *
 * Returns `null` if [arena] runs out of capacity, and throws [FlatHashLifeArenaException] if the pattern has too many
 * cells or does not fit the arena's levels or coordinate range.
 */
internal fun buildQuadtreeBottomUp(cellState: CellState, arena: FlatHashLifeArena): Pair<IntOffset, UInt>? {
    val cells = cellState.aliveCells
    // A set reports `Int.MAX_VALUE` when it holds at least that many cells, more than an array can hold.
    if (cells.size == Int.MAX_VALUE) {
        throw FlatHashLifeArenaException("Pattern has too many live cells to import into FlatHashLifeArena")
    }
    val keys = ArrayList<Any?>(cells.size)
    for (cell in cells) {
        keys.add(cellKeyOf(cell))
    }
    val (cornerX, cornerYAndMacroCell) = f_Algorithm_cellsToMacroCell(keys.toTypedArray())
    val (cornerY, macroCell) = cornerYAndMacroCell
    return internMacroCellDag(
        HashLifeCellState(IntOffset(keyCoordinate(cornerX), keyCoordinate(cornerY)), macroCell),
        arena,
    )
}

/**
 * Imports a [HashLifeCellState] into [arena] using a DAG-based bottom-up traversal with subtree memoization.
 *
 * This avoids exponential tree traversal costs on highly repetitive patterns where identical subtrees
 * are shared across quadrants. A level 4 root is imported as its centered level 6 expansion.
 *
 * Returns `null` if [arena] runs out of capacity, and throws [FlatHashLifeArenaException] if the pattern is above
 * level 60 or its expansion does not fit the arena's coordinate range.
 */
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

    // The memoized recursion modeled by `DagIntern` in Lean: each node is imported by `importMacroCellNode` from the
    // ids of its children. The memo is keyed by identity: structural equality of `MacroCell` does not short-circuit
    // on shared children, so comparing two equal but separately built subtrees walks every path through them.
    val memo = mutableMapOf<IdentityKey, UInt>()

    fun intern(node: MacroCell): UInt {
        val key = IdentityKey(node)
        memo[key]?.let { return it }
        val id = if (f_Algorithm_importNeedsChildren(node)) {
            val cellNode = node as MacroCell.CellNode
            val nwId = intern(cellNode.nw)
            val neId = intern(cellNode.ne)
            val swId = intern(cellNode.sw)
            val seId = intern(cellNode.se)
            arena.importMacroCellNode(node, nwId, neId, swId, seId)
        } else {
            arena.importMacroCellNode(node, UNCOMPUTED_ID, UNCOMPUTED_ID, UNCOMPUTED_ID, UNCOMPUTED_ID)
        }
        memo[key] = id
        return id
    }

    val rootId = intern(root)
    return when {
        rootId != UNCOMPUTED_ID -> cellState.offset to rootId
        arena.overflow != 0u.toUByte() -> null
        else -> throw FlatHashLifeArenaException("Pattern exceeds the levels of FlatHashLifeArena")
    }
}

/**
 * A [MacroCell] compared by identity, so a memo lookup costs one hash and one reference comparison.
 */
private class IdentityKey(val node: MacroCell) {
    override fun equals(other: Any?): Boolean = other is IdentityKey && other.node === node

    override fun hashCode(): Int = node.hashCode()
}

/**
 * A [CellState] backed directly by the append-only structural arrays of a [FlatHashLifeArena] epoch.
 *
 * Within an arena epoch, every structural slot is write-once within an arena and never mutated after creation.
 * This allows $O(1)$ zero-copy snapshot creation per generation and $O(1)$ root handoff on consecutive steps,
 * while allowing the UI thread to traverse the quadtree lock-free without allocating `MacroCell` objects: the cell
 * iterators lazily run the verified Lean cell cursor, which emits the live cells of one leaf per step.
 */
internal class FlatHashLifeCellState(val offset: IntOffset, val rootNodeId: UInt, val arena: FlatHashLifeArena) :
    CellState() {

    private val population: ULong = arena.cellPop[rootNodeId.toInt()]

    override val aliveCells: Set<IntOffset> =
        object : Set<IntOffset> {
            // Like other collections, the set reports at most `Int.MAX_VALUE` elements.
            override val size: Int = population.coerceAtMost(Int.MAX_VALUE.toULong()).toInt()

            override fun contains(element: IntOffset): Boolean = containsOffset(element)

            override fun containsAll(elements: Collection<IntOffset>): Boolean = elements.all(::containsOffset)

            override fun isEmpty(): Boolean = size == 0

            override fun iterator(): Iterator<IntOffset> = AllCellsIterator(
                arena = arena,
                stack = arena.cellCursorStart(rootNodeId, offset.x, offset.y),
                expectedCount = population,
            )
        }

    /**
     * Whether every live cell lies in the `Int` coordinate range: whether the root's square does
     * (`flat_rootFitsInIntRange_sound` in Lean), or else whether the cursors over the cells at or past `x = 2^31` and
     * at or past `y = 2^31` (`flat_fitsInIntRange_correct`) emit nothing. They skip every subtree that misses those
     * regions, so this only visits the nodes along the edge of the range.
     */
    internal fun fitsInIntRange(): Boolean {
        // The O(1) check of the root's square (`flat_rootFitsInIntRange_sound`) settles almost every state.
        if (arena.rootFitsInIntRange(rootNodeId, offset.x, offset.y)) return true
        val start = arena.cellCursorStart(rootNodeId, offset.x, offset.y)
        return !arena.emitsAnyCellPastX(start) && !arena.emitsAnyCellPastY(start)
    }

    private fun containsOffset(element: IntOffset): Boolean = arena.containsCell(
        rootNodeId,
        element.x.toLong() - offset.x.toLong(),
        element.y.toLong() - offset.y.toLong(),
    )

    override fun offsetBy(offset: IntOffset): CellState {
        val shifted = FlatHashLifeCellState(
            offset = this.offset + offset,
            rootNodeId = rootNodeId,
            arena = arena,
        )
        // A shift can move cells past `Int.MAX_VALUE`, which the arena cannot list; wrap them like other states do.
        return if (shifted.fitsInIntRange()) shifted else CellState(aliveCells.mapTo(HashSet()) { it + offset })
    }

    override fun withCell(offset: IntOffset, isAlive: Boolean): CellState = if (containsOffset(offset) == isAlive) {
        this
    } else {
        toHashLifeCellState().withCell(offset, isAlive)
    }

    override fun getAliveCellsInWindow(cellWindow: CellWindow): Iterable<IntOffset> = Iterable {
        WindowCellsIterator(
            arena = arena,
            stack = arena.cellCursorStart(rootNodeId, offset.x, offset.y),
            cellWindow = cellWindow,
        )
    }

    override fun toString(): String = "FlatHashLifeCellState(${aliveCells.toSet()})"
}

/**
 * Lazily iterates the cells the Lean cell cursor emits, as `cellCursorRun` (`flat_cellCursorAll_correct` and
 * `flat_cellCursorInWindow_correct`) runs it: [step] is called until the stack is empty, and the set bits of each
 * emitted mask, in increasing order, are the cells `leafChunkKey` names.
 *
 * Each step calls an `...Into` member of the arena, which passes the step's result (the `leafRowMask` of the cells it
 * emits, zero for none, the top-left corner of their leaf, and the new stack) to an inline lambda instead of
 * returning a tuple (`flat_cellCursorStepInto_eq`), so a step allocates no tuple.
 *
 * With an [expectedCount], iteration fails if the cursor emits a different number of cells, which happens when some
 * live cells lie past the `Int` coordinate range.
 */
private abstract class CellCursorIterator(protected var stack: Any?, private val expectedCount: ULong?) :
    Iterator<IntOffset> {
    protected var mask = 0uL
    protected var x0 = 0L
    protected var y0 = 0L
    private var count = 0uL

    /** Runs one step of the cursor on [stack], storing its result in [mask], [x0], [y0] and [stack]. */
    protected abstract fun step()

    override fun hasNext(): Boolean {
        while (mask == 0uL && !f_Algorithm_cellCursorDone(stack)) {
            step()
        }
        if (mask == 0uL && expectedCount != null && count != expectedCount) {
            throw FlatHashLifeArenaException("Pattern exceeds the coordinate range of FlatHashLifeArena")
        }
        return mask != 0uL
    }

    override fun next(): IntOffset {
        if (!hasNext()) throw NoSuchElementException()
        val k = mask.countTrailingZeroBits()
        mask = mask and (mask - 1uL)
        count++
        return keyCell(f_Algorithm_leafChunkKey(x0, y0, k.toUInt()))
    }
}

/** The cells with 32-bit coordinates (`cellCursorStepAll`). */
private class AllCellsIterator(private val arena: FlatHashLifeArena, stack: Any?, expectedCount: ULong) :
    CellCursorIterator(stack, expectedCount) {
    override fun step() {
        arena.cellCursorStepAllInto(stack) { chunk, chunkX0, chunkY0, nextStack ->
            mask = chunk
            x0 = chunkX0
            y0 = chunkY0
            stack = nextStack
        }
    }
}

/** The cells in [cellWindow] (`cellCursorStepInWindow`). */
private class WindowCellsIterator(
    private val arena: FlatHashLifeArena,
    stack: Any?,
    private val cellWindow: CellWindow,
) : CellCursorIterator(stack, expectedCount = null) {
    override fun step() {
        arena.cellCursorStepInWindowInto(
            cellWindow.left,
            cellWindow.top,
            cellWindow.right,
            cellWindow.bottom,
            stack,
        ) { chunk, chunkX0, chunkY0, nextStack ->
            mask = chunk
            x0 = chunkX0
            y0 = chunkY0
            stack = nextStack
        }
    }
}

/** Whether the Lean cell cursor over the cells with `x ≥ 2^31` (`cellCursorStepPastX`), run from [start], emits any. */
private fun FlatHashLifeArena.emitsAnyCellPastX(start: Any?): Boolean {
    var stack = start
    var mask = 0uL
    while (mask == 0uL && !f_Algorithm_cellCursorDone(stack)) {
        cellCursorStepPastXInto(stack) { chunk, _, _, nextStack ->
            mask = chunk
            stack = nextStack
        }
    }
    return mask != 0uL
}

/** Whether the Lean cell cursor over the cells with `y ≥ 2^31` (`cellCursorStepPastY`), run from [start], emits any. */
private fun FlatHashLifeArena.emitsAnyCellPastY(start: Any?): Boolean {
    var stack = start
    var mask = 0uL
    while (mask == 0uL && !f_Algorithm_cellCursorDone(stack)) {
        cellCursorStepPastYInto(stack) { chunk, _, _, nextStack ->
            mask = chunk
            stack = nextStack
        }
    }
    return mask != 0uL
}

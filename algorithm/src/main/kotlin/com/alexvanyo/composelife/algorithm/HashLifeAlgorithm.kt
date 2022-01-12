package com.alexvanyo.composelife.algorithm

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.CellState
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.withContext
import kotlin.math.ceil
import kotlin.math.log2

@Suppress("TooManyFunctions")
class HashLifeAlgorithm(
    private val backgroundDispatcher: CoroutineDispatcher,
) : GameOfLifeAlgorithm {

    /**
     * The map containing the "canonical" [MacroCell.CellNode]s. This ensures that there is exactly one instance of
     * each equivalent [MacroCell.CellNode] (which makes comparing [MacroCell.CellNode]s possible with just reference
     * checking).
     *
     * TODO: Prune this map as needed.
     */
    private val canonicalCellMap = mutableMapOf<MacroCell.CellNode, MacroCell.CellNode>()

    /**
     * The memoization map for [MacroCell.CellNode.computeNextGeneration].
     *
     * TODO: Prune this map as needed.
     */
    private val cellMap = mutableMapOf<MacroCell.CellNode, MacroCell.CellNode>()

    /**
     * The memoization map for [MacroCell.size].
     *
     * TODO: Prune this map as needed.
     */
    private val cellSizeMap = mutableMapOf<MacroCell.CellNode, Int>()

    /**
     * Computes the next generation for the given [MacroCell.CellNode].
     *
     * For simplicity, this function will return a [MacroCell.CellNode] that is half as big, centered on this node.
     * (in other words, a [MacroCell.CellNode] with a decremented level).
     *
     * This function is memoized by [cellMap].
     */
    @Suppress("LongMethod", "ComplexMethod")
    private fun MacroCell.CellNode.computeNextGeneration(): MacroCell.CellNode {
        require(level >= 2)
        val alreadyComputed = cellMap[this]
        if (alreadyComputed != null) return alreadyComputed

        nw as MacroCell.CellNode
        ne as MacroCell.CellNode
        sw as MacroCell.CellNode
        se as MacroCell.CellNode

        val computed = if (level == 2) {
            nw.nw as MacroCell.Cell
            nw.ne as MacroCell.Cell
            nw.sw as MacroCell.Cell
            nw.se as MacroCell.Cell
            ne.nw as MacroCell.Cell
            ne.ne as MacroCell.Cell
            ne.sw as MacroCell.Cell
            ne.se as MacroCell.Cell
            sw.nw as MacroCell.Cell
            sw.ne as MacroCell.Cell
            sw.sw as MacroCell.Cell
            sw.se as MacroCell.Cell
            se.nw as MacroCell.Cell
            se.ne as MacroCell.Cell
            se.sw as MacroCell.Cell
            se.se as MacroCell.Cell

            val nwCount = listOf(
                nw.nw.isAlive,
                nw.ne.isAlive,
                ne.nw.isAlive,
                nw.sw.isAlive,
                ne.sw.isAlive,
                sw.nw.isAlive,
                sw.ne.isAlive,
                se.nw.isAlive
            ).count { it }
            val newNw = when (nw.se) {
                MacroCell.Cell.AliveCell -> if (nwCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (nwCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val neCount = listOf(
                nw.ne.isAlive,
                ne.nw.isAlive,
                ne.ne.isAlive,
                nw.se.isAlive,
                ne.se.isAlive,
                sw.ne.isAlive,
                se.nw.isAlive,
                se.ne.isAlive
            ).count { it }
            val newNe = when (ne.sw) {
                MacroCell.Cell.AliveCell -> if (neCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (neCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val swCount = listOf(
                nw.sw.isAlive,
                nw.se.isAlive,
                ne.sw.isAlive,
                sw.nw.isAlive,
                se.nw.isAlive,
                sw.sw.isAlive,
                sw.se.isAlive,
                se.sw.isAlive
            ).count { it }
            val newSw = when (sw.ne) {
                MacroCell.Cell.AliveCell -> if (swCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (swCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val seCount = listOf(
                nw.se.isAlive,
                ne.sw.isAlive,
                ne.se.isAlive,
                sw.ne.isAlive,
                se.ne.isAlive,
                sw.se.isAlive,
                se.sw.isAlive,
                se.se.isAlive
            ).count { it }
            val newSe = when (se.nw) {
                MacroCell.Cell.AliveCell -> if (seCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (seCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            MacroCell.CellNode(
                nw = newNw,
                ne = newNe,
                sw = newSw,
                se = newSe
            ).makeCanonical()
        } else {
            val n00 = centeredSubnode(nw)
            val n01 = centeredHorizontal(nw, ne)
            val n02 = centeredSubnode(ne)
            val n10 = centeredVertical(nw, sw)
            val n11 = centeredSubSubnode(this)
            val n12 = centeredVertical(ne, se)
            val n20 = centeredSubnode(sw)
            val n21 = centeredHorizontal(sw, se)
            val n22 = centeredSubnode(se)

            MacroCell.CellNode(
                nw = MacroCell.CellNode(
                    nw = n00,
                    ne = n01,
                    sw = n10,
                    se = n11
                ).makeCanonical().computeNextGeneration(),
                ne = MacroCell.CellNode(
                    nw = n01,
                    ne = n02,
                    sw = n11,
                    se = n12
                ).makeCanonical().computeNextGeneration(),
                sw = MacroCell.CellNode(
                    nw = n10,
                    ne = n11,
                    sw = n20,
                    se = n21
                ).makeCanonical().computeNextGeneration(),
                se = MacroCell.CellNode(
                    nw = n11,
                    ne = n12,
                    sw = n21,
                    se = n22
                ).makeCanonical().computeNextGeneration(),
            ).makeCanonical()
        }

        cellMap[this] = computed
        return computed
    }

    private fun centeredSubnode(node: MacroCell.CellNode): MacroCell.CellNode {
        node.nw as MacroCell.CellNode
        node.ne as MacroCell.CellNode
        node.sw as MacroCell.CellNode
        node.se as MacroCell.CellNode
        return MacroCell.CellNode(
            nw = node.nw.se,
            ne = node.ne.sw,
            sw = node.sw.ne,
            se = node.se.nw
        ).makeCanonical()
    }

    private fun centeredHorizontal(w: MacroCell.CellNode, e: MacroCell.CellNode): MacroCell.CellNode {
        w.ne as MacroCell.CellNode
        w.se as MacroCell.CellNode
        e.nw as MacroCell.CellNode
        e.sw as MacroCell.CellNode
        return MacroCell.CellNode(
            nw = w.ne.se,
            ne = e.nw.sw,
            sw = w.se.ne,
            se = e.sw.nw
        ).makeCanonical()
    }

    private fun centeredVertical(n: MacroCell.CellNode, s: MacroCell.CellNode): MacroCell.CellNode {
        n.se as MacroCell.CellNode
        n.sw as MacroCell.CellNode
        s.nw as MacroCell.CellNode
        s.ne as MacroCell.CellNode
        return MacroCell.CellNode(
            nw = n.sw.se,
            ne = n.se.sw,
            sw = s.nw.ne,
            se = s.ne.nw
        ).makeCanonical()
    }

    private fun centeredSubSubnode(node: MacroCell.CellNode): MacroCell.CellNode {
        node.nw as MacroCell.CellNode
        node.ne as MacroCell.CellNode
        node.sw as MacroCell.CellNode
        node.se as MacroCell.CellNode
        node.nw.se as MacroCell.CellNode
        node.ne.sw as MacroCell.CellNode
        node.sw.ne as MacroCell.CellNode
        node.se.nw as MacroCell.CellNode
        return MacroCell.CellNode(
            nw = node.nw.se.se,
            ne = node.ne.sw.sw,
            sw = node.sw.ne.ne,
            se = node.se.nw.nw
        ).makeCanonical()
    }

    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState =
        withContext(backgroundDispatcher) {
            computeGenerationWithStepImpl(
                cellState = cellState.toHashLifeCellState(),
                step = step
            )
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: HashLifeCellState,
        @IntRange(from = 0) step: Int,
    ): HashLifeCellState =
        if (step == 0) {
            cellState
        } else {
            computeGenerationWithStepImpl(
                cellState = computeNextGeneration(cellState),
                step = step - 1
            )
        }

    /**
     * Returns the [HashLifeCellState] corresponding to the next generation.
     */
    @Suppress("ComplexMethod")
    private tailrec fun computeNextGeneration(cellState: HashLifeCellState): HashLifeCellState {
        val node = cellState.macroCell as MacroCell.CellNode

        if (node.level > 3) {
            node.nw as MacroCell.CellNode
            node.nw.nw as MacroCell.CellNode
            node.nw.ne as MacroCell.CellNode
            node.nw.sw as MacroCell.CellNode
            node.nw.se as MacroCell.CellNode
            node.ne as MacroCell.CellNode
            node.ne.nw as MacroCell.CellNode
            node.ne.ne as MacroCell.CellNode
            node.ne.sw as MacroCell.CellNode
            node.ne.se as MacroCell.CellNode
            node.sw as MacroCell.CellNode
            node.sw.nw as MacroCell.CellNode
            node.sw.ne as MacroCell.CellNode
            node.sw.sw as MacroCell.CellNode
            node.sw.se as MacroCell.CellNode
            node.se as MacroCell.CellNode
            node.se.nw as MacroCell.CellNode
            node.se.ne as MacroCell.CellNode
            node.se.sw as MacroCell.CellNode
            node.se.se as MacroCell.CellNode

            @Suppress("ComplexCondition")
            if (node.nw.nw.size() == 0 && node.nw.ne.size() == 0 && node.nw.ne.size() == 0 &&
                node.nw.se.nw.size() == 0 && node.nw.se.ne.size() == 0 && node.nw.se.sw.size() == 0 &&
                node.ne.nw.size() == 0 && node.ne.ne.size() == 0 && node.ne.se.size() == 0 &&
                node.ne.sw.nw.size() == 0 && node.ne.sw.ne.size() == 0 && node.ne.sw.se.size() == 0 &&
                node.sw.nw.size() == 0 && node.sw.sw.size() == 0 && node.sw.se.size() == 0 &&
                node.sw.ne.nw.size() == 0 && node.sw.ne.sw.size() == 0 && node.sw.ne.se.size() == 0 &&
                node.se.ne.size() == 0 && node.se.sw.size() == 0 && node.se.se.size() == 0 &&
                node.se.nw.ne.size() == 0 && node.se.nw.sw.size() == 0 && node.se.nw.se.size() == 0
            ) {
                return HashLifeCellState(
                    offset = cellState.offset + IntOffset(1 shl (node.level - 2), 1 shl (node.level - 2)),
                    macroCell = cellState.macroCell.computeNextGeneration()
                )
            }
        }

        // If our primary macro cell would be too small or the resulting macro cell wouldn't be the correct result
        // (due to an expanding pattern), expand the main macro cell and compute.
        return computeNextGeneration(cellState.expandCentered())
    }

    private fun MacroCell.size(): Int =
        when (this) {
            MacroCell.Cell.AliveCell -> 1
            MacroCell.Cell.DeadCell -> 0
            is MacroCell.CellNode -> {
                cellSizeMap.getOrPut(this) {
                    nw.size() + ne.size() + sw.size() + se.size()
                }
            }
        }

    private fun HashLifeCellState.expandCentered(): HashLifeCellState {
        val node = macroCell as MacroCell.CellNode

        val sameLevelEmptyCell = createEmptyMacroCell(node.level)
        val smallerLevelEmptyCell = createEmptyMacroCell(node.level - 1)

        val cell = MacroCell.CellNode(
            nw = MacroCell.CellNode(
                nw = sameLevelEmptyCell,
                ne = sameLevelEmptyCell,
                sw = sameLevelEmptyCell,
                se = MacroCell.CellNode(
                    nw = smallerLevelEmptyCell,
                    ne = smallerLevelEmptyCell,
                    sw = smallerLevelEmptyCell,
                    se = node.nw
                ).makeCanonical()
            ).makeCanonical(),
            ne = MacroCell.CellNode(
                nw = sameLevelEmptyCell,
                ne = sameLevelEmptyCell,
                sw = MacroCell.CellNode(
                    nw = smallerLevelEmptyCell,
                    ne = smallerLevelEmptyCell,
                    sw = node.ne,
                    se = smallerLevelEmptyCell
                ).makeCanonical(),
                se = sameLevelEmptyCell
            ).makeCanonical(),
            sw = MacroCell.CellNode(
                nw = sameLevelEmptyCell,
                ne = MacroCell.CellNode(
                    nw = smallerLevelEmptyCell,
                    ne = node.sw,
                    sw = smallerLevelEmptyCell,
                    se = smallerLevelEmptyCell
                ).makeCanonical(),
                sw = sameLevelEmptyCell,
                se = sameLevelEmptyCell
            ).makeCanonical(),
            se = MacroCell.CellNode(
                nw = MacroCell.CellNode(
                    nw = node.se,
                    ne = smallerLevelEmptyCell,
                    sw = smallerLevelEmptyCell,
                    se = smallerLevelEmptyCell
                ).makeCanonical(),
                ne = sameLevelEmptyCell,
                sw = sameLevelEmptyCell,
                se = sameLevelEmptyCell
            ).makeCanonical()
        )

        val offsetDiff = 3 * (1 shl (node.level - 1))

        return HashLifeCellState(
            offset = offset + IntOffset(-offsetDiff, -offsetDiff),
            macroCell = cell
        )
    }

    private fun CellState.toHashLifeCellState(): HashLifeCellState {
        if (this is HashLifeCellState) return this

        val xValues = aliveCells.map { it.x }
        val yValues = aliveCells.map { it.y }
        val minX = xValues.minOrNull() ?: 0
        val maxX = xValues.maxOrNull() ?: 0
        val minY = yValues.minOrNull() ?: 0
        val maxY = yValues.maxOrNull() ?: 0

        val minimumLevel = ceil(
            maxOf(
                log2((maxX - minX).toDouble()),
                log2((maxY - minY).toDouble())
            )
        ).toInt().coerceAtLeast(3)

        val offset = IntOffset(minX, minY)
        val macroCell = createMacroCell(
            cellState = this,
            offset = offset,
            level = minimumLevel
        )

        return HashLifeCellState(
            offset = offset,
            macroCell = macroCell
        )
    }

    private fun createEmptyMacroCell(level: Int): MacroCell =
        if (level == 0) {
            MacroCell.Cell.DeadCell
        } else {
            val smallerEmptyMacroCell = createEmptyMacroCell(level - 1)
            MacroCell.CellNode(
                smallerEmptyMacroCell,
                smallerEmptyMacroCell,
                smallerEmptyMacroCell,
                smallerEmptyMacroCell
            ).makeCanonical()
        }

    private fun createMacroCell(cellState: CellState, offset: IntOffset, level: Int): MacroCell =
        if (level == 0) {
            if (offset in cellState.aliveCells) {
                MacroCell.Cell.AliveCell
            } else {
                MacroCell.Cell.DeadCell
            }
        } else {
            val offsetDiff = 1 shl (level - 1)
            MacroCell.CellNode(
                createMacroCell(cellState, offset, level - 1),
                createMacroCell(cellState, offset + IntOffset(offsetDiff, 0), level - 1),
                createMacroCell(cellState, offset + IntOffset(0, offsetDiff), level - 1),
                createMacroCell(cellState, offset + IntOffset(offsetDiff, offsetDiff), level - 1),
            ).makeCanonical()
        }

    private fun MacroCell.withCell(target: IntOffset, isAlive: Boolean): MacroCell =
        when (this) {
            MacroCell.Cell.AliveCell,
            MacroCell.Cell.DeadCell -> {
                require(target == IntOffset.Zero)
                if (isAlive) {
                    MacroCell.Cell.AliveCell
                } else {
                    MacroCell.Cell.DeadCell
                }
            }
            is MacroCell.CellNode -> {
                val offsetDiff = 1 shl (level - 1)
                val isNorth = target.y < offsetDiff
                val isWest = target.x < offsetDiff
                if (isNorth) {
                    if (isWest) {
                        MacroCell.CellNode(
                            nw = nw.withCell(target, isAlive),
                            ne = ne,
                            sw = sw,
                            se = se
                        ).makeCanonical()
                    } else {
                        MacroCell.CellNode(
                            nw = nw,
                            ne = ne.withCell(target + IntOffset(-offsetDiff, 0), isAlive),
                            sw = sw,
                            se = se
                        ).makeCanonical()
                    }
                } else {
                    if (isWest) {
                        MacroCell.CellNode(
                            nw = nw,
                            ne = ne,
                            sw = sw.withCell(target + IntOffset(0, -offsetDiff), isAlive),
                            se = se
                        ).makeCanonical()
                    } else {
                        MacroCell.CellNode(
                            nw = nw,
                            ne = ne,
                            sw = sw,
                            se = se.withCell(target + IntOffset(-offsetDiff, -offsetDiff), isAlive)
                        ).makeCanonical()
                    }
                }
            }
        }

    private fun MacroCell.iterator(
        offset: IntOffset,
    ): Iterator<IntOffset> = iterator {
        when (this@iterator) {
            MacroCell.Cell.AliveCell -> yield(offset)
            MacroCell.Cell.DeadCell -> Unit
            is MacroCell.CellNode -> {
                val offsetDiff = 1 shl (level - 1)
                yieldAll(nw.iterator(offset))
                yieldAll(ne.iterator(offset + IntOffset(offsetDiff, 0)))
                yieldAll(sw.iterator(offset + IntOffset(0, offsetDiff)))
                yieldAll(se.iterator(offset + IntOffset(offsetDiff, offsetDiff)))
            }
        }
    }

    @Suppress("NestedBlockDepth")
    private fun MacroCell.contains(target: IntOffset): Boolean =
        when (this) {
            MacroCell.Cell.AliveCell -> {
                require(target == IntOffset.Zero)
                true
            }
            MacroCell.Cell.DeadCell -> {
                require(target == IntOffset.Zero)
                false
            }
            is MacroCell.CellNode -> {
                if (size() == 0) {
                    false
                } else {
                    val offsetDiff = 1 shl (level - 1)
                    val isNorth = target.y < offsetDiff
                    val isWest = target.x < offsetDiff
                    if (isNorth) {
                        if (isWest) {
                            nw.contains(target)
                        } else {
                            ne.contains(target + IntOffset(-offsetDiff, 0))
                        }
                    } else {
                        if (isWest) {
                            sw.contains(target + IntOffset(0, -offsetDiff))
                        } else {
                            se.contains(target + IntOffset(-offsetDiff, -offsetDiff))
                        }
                    }
                }
            }
        }

    private fun MacroCell.CellNode.makeCanonical(): MacroCell.CellNode =
        canonicalCellMap.getOrPut(this) { this }

    private inner class HashLifeCellState(
        val offset: IntOffset,
        val macroCell: MacroCell,
    ) : CellState() {
        init {
            // Check the invariant for the macroCell
            check(macroCell.level >= 3)
        }

        override val aliveCells: Set<IntOffset> = object : Set<IntOffset> {
            override val size: Int by lazy {
                macroCell.size()
            }

            override fun contains(element: IntOffset): Boolean {
                val target = element - offset
                val size = 1 shl macroCell.level
                return if (target.x in 0 until size && target.y in 0 until size) {
                    macroCell.contains(target)
                } else {
                    false
                }
            }

            override fun containsAll(elements: Collection<IntOffset>): Boolean = elements.all { contains(it) }

            override fun isEmpty(): Boolean = size == 0

            override fun iterator(): Iterator<IntOffset> = macroCell.iterator(offset)
        }

        override fun offsetBy(offset: IntOffset) = HashLifeCellState(
            offset = this.offset + offset,
            macroCell = macroCell
        )

        override fun withCell(offset: IntOffset, isAlive: Boolean): CellState {
            var hashLifeCellState = this

            var target: IntOffset

            while (
                run {
                    target = offset - hashLifeCellState.offset
                    val size = 1 shl hashLifeCellState.macroCell.level
                    target.x !in 0 until size || target.y !in 0 until size
                }
            ) {
                hashLifeCellState = hashLifeCellState.expandCentered()
            }

            return HashLifeCellState(
                offset = hashLifeCellState.offset,
                macroCell = hashLifeCellState.macroCell.withCell(target, isAlive)
            )
        }

        override fun toString(): String = "HashLifeCellState(${aliveCells.toSet()})"
    }
}

private sealed class MacroCell {

    abstract val level: Int

    sealed class Cell : MacroCell() {

        override val level = 0

        abstract val isAlive: Boolean

        object AliveCell : Cell() {
            override val isAlive = true
        }

        object DeadCell : Cell() {
            override val isAlive = false
        }
    }

    data class CellNode(
        val nw: MacroCell,
        val ne: MacroCell,
        val sw: MacroCell,
        val se: MacroCell,
    ) : MacroCell() {
        override val level = nw.level + 1

        val hashCode by lazy {
            var hash = level
            hash *= 31
            hash += nw.hashCode()
            hash *= 31
            hash += ne.hashCode()
            hash *= 31
            hash += sw.hashCode()
            hash *= 31
            hash += se.hashCode()
            hash
        }

        override fun hashCode(): Int = hashCode

        override fun equals(other: Any?): Boolean =
            if (other !is CellNode) {
                false
            } else {
                other.level == level &&
                    other.nw === nw &&
                    other.ne === ne &&
                    other.sw === sw &&
                    other.se === se
            }
    }
}

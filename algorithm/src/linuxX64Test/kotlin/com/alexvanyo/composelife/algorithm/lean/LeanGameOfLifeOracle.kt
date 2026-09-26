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

package com.alexvanyo.composelife.algorithm.lean

import com.alexvanyo.composelife.algorithm.lean.cinterop.CellGridC
import com.alexvanyo.composelife.algorithm.lean.cinterop.CellPointC
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_centered_horizontal_subnode_level3_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_centered_sub_subnode_level4_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_centered_subnode_level3_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_centered_vertical_subnode_level3_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_free_grid
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_init_runtime
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_step
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_step_4x4_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_step_leaf_bits
import com.alexvanyo.composelife.algorithm.lean.cinterop.lean_algorithm_step_level4_bits
import com.alexvanyo.composelife.geometry.IntOffset
import com.alexvanyo.composelife.model.MacroCell
import kotlinx.cinterop.ExperimentalForeignApi
import kotlinx.cinterop.alloc
import kotlinx.cinterop.allocArray
import kotlinx.cinterop.convert
import kotlinx.cinterop.get
import kotlinx.cinterop.memScoped
import kotlinx.cinterop.ptr

/**
 * An in-memory differential oracle running the formal Lean 4 Conway Game of Life specification.
 */
@OptIn(ExperimentalForeignApi::class)
internal class LeanGameOfLifeOracle {
    init {
        lean_algorithm_init_runtime()
    }

    /**
     * Steps a 4x4 bitfield to its 2x2 central next generation using the formal Lean specification.
     */
    fun step4x4Bits(bits: Int): Int = lean_algorithm_step_4x4_bits(bits.toUShort()).toInt()

    /**
     * Steps an 8x8 64-bit leaf node to its 4x4 central next generation using the formal Lean specification.
     */
    fun stepLeafBits(bits: Long): Int = lean_algorithm_step_leaf_bits(bits.toULong()).toInt()

    /**
     * Steps a 16x16 Level 4 node (four 8x8 leaf nodes) to its central 8x8 next generation leaf node
     * using the formal Lean specification.
     */
    fun stepLevel4Bits(nw: Long, ne: Long, sw: Long, se: Long): Long = lean_algorithm_step_level4_bits(
        nw = nw.toULong(),
        ne = ne.toULong(),
        sw = sw.toULong(),
        se = se.toULong(),
    ).toLong()

    /**
     * Steps a [MacroCell.Level4Node] to its central 8x8 next generation [MacroCell.LeafNode]
     * using the formal Lean specification.
     */
    fun stepLevel4(node: MacroCell.Level4Node): MacroCell.LeafNode = stepLevel4Bits(node.nw, node.ne, node.sw, node.se)

    /**
     * Extracts the central 4x4 from an 8x8 64-bit leaf node using the formal Lean specification.
     */
    fun centeredSubnodeLevel3(leaf: MacroCell.LeafNode): Int =
        lean_algorithm_centered_subnode_level3_bits(leaf.toULong()).toInt()

    /**
     * Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes using the formal Lean specification.
     */
    fun centeredHorizontalSubnodeLevel3(w: MacroCell.LeafNode, e: MacroCell.LeafNode): Int =
        lean_algorithm_centered_horizontal_subnode_level3_bits(w.toULong(), e.toULong()).toInt()

    /**
     * Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes using the formal Lean specification.
     */
    fun centeredVerticalSubnodeLevel3(n: MacroCell.LeafNode, s: MacroCell.LeafNode): Int =
        lean_algorithm_centered_vertical_subnode_level3_bits(n.toULong(), s.toULong()).toInt()

    /**
     * Extracts the central 4x4 from a 16x16 Level 4 node using the formal Lean specification.
     */
    fun centeredSubSubnodeLevel4(
        nw: MacroCell.LeafNode,
        ne: MacroCell.LeafNode,
        sw: MacroCell.LeafNode,
        se: MacroCell.LeafNode,
    ): Int = lean_algorithm_centered_sub_subnode_level4_bits(
        nw = nw.toULong(),
        ne = ne.toULong(),
        sw = sw.toULong(),
        se = se.toULong(),
    ).toInt()

    /**
     * Extracts the central 4x4 from a [MacroCell.Level4Node] using the formal Lean specification.
     */
    fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
        centeredSubSubnodeLevel4(node.nw, node.ne, node.sw, node.se)

    fun step(cells: Set<IntOffset>, stepCount: Int): Set<IntOffset> = memScoped {
        if (cells.isEmpty()) return emptySet()

        val inPoints = allocArray<CellPointC>(cells.size)
        cells.forEachIndexed { index, cell ->
            inPoints[index].x = cell.x
            inPoints[index].y = cell.y
        }

        val outGrid = alloc<CellGridC>()

        val res = lean_algorithm_step(
            in_points = inPoints,
            in_count = cells.size.convert(),
            step = stepCount.toUInt(),
            out_grid = outGrid.ptr,
        )
        check(res == 0) { "lean_algorithm_step failed with error code $res" }

        try {
            buildSet {
                val count = outGrid.count.toInt()
                val points = outGrid.points
                if (points != null) {
                    for (i in 0 until count) {
                        add(IntOffset(points[i].x, points[i].y))
                    }
                }
            }
        } finally {
            lean_algorithm_free_grid(outGrid.ptr)
        }
    }
}

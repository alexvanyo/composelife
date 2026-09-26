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

package com.alexvanyo.composelife.model

import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

class MacroCellHashCodeTests {

    @Test
    fun empty_nodes_at_different_levels_have_distinct_hashes() {
        val emptyHashes = (4..30).map { level ->
            createEmptyMacroCell(level).hashCode()
        }.toSet()

        assertEquals(27, emptyHashes.size, "Empty nodes at different levels must have distinct hashes")
    }

    @Test
    fun level4_quadrant_permutations_have_distinct_hashes() {
        val leafA = 0x0123_4567_89AB_CDEFL
        val leafB = 0xFEDC_BA98_7654_3210uL.toLong()
        val leafC = 0x5555_AAAA_5555_AAAAL
        val leafD = 0x3333_CCCC_3333_CCCCL

        val n1 = MacroCell.Level4Node(leafA, leafB, leafC, leafD)
        val n2 = MacroCell.Level4Node(leafB, leafA, leafC, leafD)
        val n3 = MacroCell.Level4Node(leafA, leafC, leafB, leafD)
        val n4 = MacroCell.Level4Node(leafD, leafC, leafB, leafA)

        val hashes = setOf(n1.hashCode(), n2.hashCode(), n3.hashCode(), n4.hashCode())
        assertEquals(4, hashes.size, "Quadrant permutations must not produce identical hashes")
    }

    @Test
    fun cellnode_quadrant_permutations_have_distinct_hashes() {
        val nA = MacroCell.Level4Node(1L, 0L, 0L, 0L)
        val nB = MacroCell.Level4Node(0L, 2L, 0L, 0L)
        val nC = MacroCell.Level4Node(0L, 0L, 4L, 0L)
        val nD = MacroCell.Level4Node(0L, 0L, 0L, 8L)

        val c1 = MacroCell.CellNode(nA, nB, nC, nD)
        val c2 = MacroCell.CellNode(nB, nA, nC, nD)
        val c3 = MacroCell.CellNode(nA, nC, nB, nD)
        val c4 = MacroCell.CellNode(nD, nC, nB, nA)

        val hashes = setOf(c1.hashCode(), c2.hashCode(), c3.hashCode(), c4.hashCode())
        assertEquals(4, hashes.size, "CellNode quadrant permutations must not produce identical hashes")
    }

    @Test
    fun vertically_symmetric_leaves_do_not_collide_with_zero() {
        // A pattern with identical cells in north (bits 0..31) and south (bits 32..63)
        // With Long.hashCode() = (x xor (x ushr 32)).toInt(), this would hash to 0!
        val northHalf = 0x1234_5678L
        val symmetricLeaf = northHalf or (northHalf shl 32)

        val node = MacroCell.Level4Node(symmetricLeaf, 0L, 0L, 0L)
        val emptyNode = MacroCell.Level4Node(0L, 0L, 0L, 0L)

        assertNotEquals(emptyNode.hashCode(), node.hashCode(), "Symmetric leaf must not collide with empty node")
    }

    @Test
    fun horizontally_symmetric_leaves_do_not_collide_with_zero() {
        // In Morton order, quadrant 0 is NW and quadrant 1 is NE.
        // A horizontally symmetric pattern has identical cells in q0 and q1.
        val q0 = 0x1234L
        val symmetricLeaf = q0 or (q0 shl 16)

        val node = MacroCell.Level4Node(symmetricLeaf, 0L, 0L, 0L)
        val emptyNode = MacroCell.Level4Node(0L, 0L, 0L, 0L)

        assertNotEquals(emptyNode.hashCode(), node.hashCode(), "Symmetric leaf must not collide with empty node")
    }

    @Test
    fun collision_rate_on_synthetic_level4_nodes() {
        val random = Random(42)
        val sampleSize = 100_000

        val level4Nodes = HashSet<MacroCell.Level4Node>(sampleSize)
        val level4Hashes = HashSet<Int>(sampleSize)

        repeat(sampleSize) {
            val nw = if (random.nextBoolean()) 0L else random.nextLong()
            val ne = if (random.nextBoolean()) 0L else random.nextLong()
            val sw = if (random.nextBoolean()) 0L else random.nextLong()
            val se = if (random.nextBoolean()) 0L else random.nextLong()

            val node = MacroCell.Level4Node(nw, ne, sw, se)
            level4Nodes.add(node)
            level4Hashes.add(node.hashCode())
        }

        val collisions = level4Nodes.size - level4Hashes.size
        val collisionRate = collisions.toDouble() / level4Nodes.size
        println("Level4Node collisions: $collisions / ${level4Nodes.size} (${collisionRate * 100}%)")

        // For a 32-bit hash space and 100,000 items, birthday paradox expects ~1.16 collisions.
        assertTrue(collisions < 15, "Too many Level4Node collisions: $collisions")
    }

    @Test
    fun collision_rate_on_synthetic_cell_nodes() {
        val random = Random(42)
        val sampleSize = 50_000

        val e4 = createEmptyMacroCell(4)
        val baseNodes = Array(100) {
            MacroCell.Level4Node(random.nextLong(), random.nextLong(), random.nextLong(), random.nextLong())
        }

        val cellNodes = HashSet<MacroCell.CellNode>(sampleSize)
        val cellHashes = HashSet<Int>(sampleSize)

        repeat(sampleSize) {
            val nw = if (random.nextBoolean()) e4 else baseNodes[random.nextInt(baseNodes.size)]
            val ne = if (random.nextBoolean()) e4 else baseNodes[random.nextInt(baseNodes.size)]
            val sw = if (random.nextBoolean()) e4 else baseNodes[random.nextInt(baseNodes.size)]
            val se = if (random.nextBoolean()) e4 else baseNodes[random.nextInt(baseNodes.size)]

            val node = MacroCell.CellNode(nw, ne, sw, se)
            cellNodes.add(node)
            cellHashes.add(node.hashCode())
        }

        val collisions = cellNodes.size - cellHashes.size
        val collisionRate = collisions.toDouble() / cellNodes.size
        println("CellNode collisions: $collisions / ${cellNodes.size} (${collisionRate * 100}%)")

        assertTrue(collisions < 10, "Too many CellNode collisions: $collisions")
    }
}

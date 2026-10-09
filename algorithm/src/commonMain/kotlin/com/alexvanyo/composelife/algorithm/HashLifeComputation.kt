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

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.model.MacroCell

/**
 * Computes the next 2x2 [Int] generation for the given 4x4 [Int] in its center.
 */
@Suppress("NOTHING_TO_INLINE")
internal inline fun Int.computeNextGeneration(): Int = f_Algorithm_exportComputeNextGen4x4UInt(this.toUInt()).toInt()

/**
 * Computes the 4x4 [Int] next generation for the given 8x8 64-bit Morton leaf node in its center.
 */
fun Long.computeNextGeneration(): Int = f_Algorithm_exportComputeLeafNextGen8x8BranchUInt(this.toULong()).toInt()

/**
 * Packs four 16-bit 4x4 quadrants in Morton order into an 8x8 64-bit leaf node.
 */
internal fun packLeafNode(nw: Int, ne: Int, sw: Int, se: Int): Long = f_Algorithm_packLeafFrom4x4sUInt(
    nw.toUInt(),
    ne.toUInt(),
    sw.toUInt(),
    se.toUInt(),
).toLong()

/**
 * Extracts the central 4x4 from an 8x8 64-bit leaf node.
 */
internal fun centeredSubnodeLevel3(node: Long): Int = f_Algorithm_centeredSubnodeLevel3BitsUInt(node.toULong()).toInt()

/**
 * Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
 */
internal fun centeredHorizontalSubnodeLevel3(w: Long, e: Long): Int =
    f_Algorithm_centeredHorizontalSubnodeLevel3BitsUInt(w.toULong(), e.toULong()).toInt()

/**
 * Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
 */
internal fun centeredVerticalSubnodeLevel3(n: Long, s: Long): Int =
    f_Algorithm_centeredVerticalSubnodeLevel3BitsUInt(n.toULong(), s.toULong()).toInt()

/**
 * Extracts the central 4x4 from a 16x16 Level 4 node consisting of four 8x8 leaf nodes.
 */
internal fun centeredSubSubnodeLevel4(nw: Long, ne: Long, sw: Long, se: Long): Int =
    f_Algorithm_centeredSubSubnodeLevel4BitsUInt(
        nw.toULong(),
        ne.toULong(),
        sw.toULong(),
        se.toULong(),
    ).toInt()

/**
 * Extracts the central 4x4 from a [MacroCell.Level4Node].
 */
internal fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
    centeredSubSubnodeLevel4(node.nw, node.ne, node.sw, node.se)

/**
 * Computes the next generation for a 16x16 Level 4 node, returning the centered 8x8 [Long] leaf node.
 */
internal fun computeLevel4NextGeneration(
    nw: Long,
    ne: Long,
    sw: Long,
    se: Long,
    computeLeafNextGen: (Long) -> Int = Long::computeNextGeneration,
): Long {
    val n00 = centeredSubnodeLevel3(nw)
    val n01 = centeredHorizontalSubnodeLevel3(nw, ne)
    val n02 = centeredSubnodeLevel3(ne)
    val n10 = centeredVerticalSubnodeLevel3(nw, sw)
    val n11 = centeredSubSubnodeLevel4(nw, ne, sw, se)
    val n12 = centeredVerticalSubnodeLevel3(ne, se)
    val n20 = centeredSubnodeLevel3(sw)
    val n21 = centeredHorizontalSubnodeLevel3(sw, se)
    val n22 = centeredSubnodeLevel3(se)

    val leafNW = packLeafNode(n00, n01, n10, n11)
    val leafNE = packLeafNode(n01, n02, n11, n12)
    val leafSW = packLeafNode(n10, n11, n20, n21)
    val leafSE = packLeafNode(n11, n12, n21, n22)

    val outNW = computeLeafNextGen(leafNW)
    val outNE = computeLeafNextGen(leafNE)
    val outSW = computeLeafNextGen(leafSW)
    val outSE = computeLeafNextGen(leafSE)

    return packLeafNode(outNW, outNE, outSW, outSE)
}

/**
 * Computes the next generation for a [MacroCell.Level4Node], returning the centered 8x8 [Long] leaf node.
 */
internal fun computeLevel4NextGeneration(
    node: MacroCell.Level4Node,
    computeLeafNextGen: (Long) -> Int = Long::computeNextGeneration,
): MacroCell.LeafNode = computeLevel4NextGeneration(
    nw = node.nw,
    ne = node.ne,
    sw = node.sw,
    se = node.se,
    computeLeafNextGen = computeLeafNextGen,
)

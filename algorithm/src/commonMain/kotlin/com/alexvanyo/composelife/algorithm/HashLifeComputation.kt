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
 * Packs four 16-bit 4x4 quadrants in Morton order into an 8x8 64-bit leaf node.
 */
internal fun packLeafNode(nw: Int, ne: Int, sw: Int, se: Int): Long = (nw.toLong() and 0xFFFFL) or
    ((ne.toLong() and 0xFFFFL) shl 16) or
    ((sw.toLong() and 0xFFFFL) shl 32) or
    ((se.toLong() and 0xFFFFL) shl 48)

/**
 * Extracts the central 4x4 from an 8x8 64-bit leaf node.
 * Matches `centeredSubnodeLevel3` in `HashLifeAlgorithm`.
 */
internal fun centeredSubnodeLevel3(node: Long): Int {
    val nw = (node and 0xFFFFL).toInt()
    val ne = ((node ushr 16) and 0xFFFFL).toInt()
    val sw = ((node ushr 32) and 0xFFFFL).toInt()
    val se = (node ushr 48).toInt()

    val q0 = (nw ushr 12) and 0xF
    val q1 = (ne ushr 8) and 0xF
    val q2 = (sw ushr 4) and 0xF
    val q3 = (se ushr 0) and 0xF

    return q0 or (q1 shl 4) or (q2 shl 8) or (q3 shl 12)
}

/**
 * Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
 * Matches `centeredHorizontalSubnodeLevel3` in `HashLifeAlgorithm`.
 */
internal fun centeredHorizontalSubnodeLevel3(w: Long, e: Long): Int {
    val wNe = ((w ushr 16) and 0xFFFFL).toInt()
    val wSe = (w ushr 48).toInt()
    val eNw = (e and 0xFFFFL).toInt()
    val eSw = ((e ushr 32) and 0xFFFFL).toInt()

    val q0 = (wNe ushr 12) and 0xF
    val q1 = (eNw ushr 8) and 0xF
    val q2 = (wSe ushr 4) and 0xF
    val q3 = (eSw ushr 0) and 0xF

    return q0 or (q1 shl 4) or (q2 shl 8) or (q3 shl 12)
}

/**
 * Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
 * Matches `centeredVerticalSubnodeLevel3` in `HashLifeAlgorithm`.
 */
internal fun centeredVerticalSubnodeLevel3(n: Long, s: Long): Int {
    val nSw = ((n ushr 32) and 0xFFFFL).toInt()
    val nSe = (n ushr 48).toInt()
    val sNw = (s and 0xFFFFL).toInt()
    val sNe = ((s ushr 16) and 0xFFFFL).toInt()

    val q0 = (nSw ushr 12) and 0xF
    val q1 = (nSe ushr 8) and 0xF
    val q2 = (sNw ushr 4) and 0xF
    val q3 = (sNe ushr 0) and 0xF

    return q0 or (q1 shl 4) or (q2 shl 8) or (q3 shl 12)
}

/**
 * Extracts the central 4x4 from a 16x16 Level 4 node consisting of four 8x8 leaf nodes.
 * Matches `centeredSubSubnodeLevel4` in `HashLifeAlgorithm`.
 */
internal fun centeredSubSubnodeLevel4(nw: Long, ne: Long, sw: Long, se: Long): Int {
    val nwSe = (nw ushr 48).toInt()
    val neSw = ((ne ushr 32) and 0xFFFFL).toInt()
    val swNe = ((sw ushr 16) and 0xFFFFL).toInt()
    val seNw = (se and 0xFFFFL).toInt()

    val q0 = (nwSe ushr 12) and 0xF
    val q1 = (neSw ushr 8) and 0xF
    val q2 = (swNe ushr 4) and 0xF
    val q3 = (seNw ushr 0) and 0xF

    return q0 or (q1 shl 4) or (q2 shl 8) or (q3 shl 12)
}

/**
 * Extracts the central 4x4 from a [MacroCell.Level4Node].
 */
internal fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
    centeredSubSubnodeLevel4(node.nw, node.ne, node.sw, node.se)

/**
 * Computes the next generation for a 16x16 Level 4 node, returning the centered 8x8 [Long] leaf node.
 * Matches `Level4Node.computeNextGeneration` in `HashLifeAlgorithm`.
 */
internal fun computeLevel4NextGeneration(
    nw: Long,
    ne: Long,
    sw: Long,
    se: Long,
    computeLeafNextGen: (Long) -> Int = Long::computeLeafNextGeneration,
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
    computeLeafNextGen: (Long) -> Int = Long::computeLeafNextGeneration,
): MacroCell.LeafNode = computeLevel4NextGeneration(
    nw = node.nw,
    ne = node.ne,
    sw = node.sw,
    se = node.se,
    computeLeafNextGen = computeLeafNextGen,
)

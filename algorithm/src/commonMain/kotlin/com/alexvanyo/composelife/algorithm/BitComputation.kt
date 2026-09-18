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

/**
 * Computes the next 2x2 [Int] generation for the given 4x4 [Int] in its center.
 */
@Suppress("NOTHING_TO_INLINE")
internal inline fun Int.computeNextGeneration(): Int {
    val count0 = (0b1110_1010_1100_1000 and this).countOneBits()
    val previousBit0 = (0b0001_0000_0000_0000 and this) shr 12
    val newBit0 = (count0 or previousBit0) xor (0b11)

    val count1 = (0b0101_1101_0100_1100 and this).countOneBits()
    val previousBit1 = (0b0000_0010_0000_0000 and this) shr 9
    val newBit1 = (count1 or previousBit1) xor (0b11)

    val count2 = (0b0011_0010_1011_1010 and this).countOneBits()
    val previousBit2 = (0b0000_0000_0100_0000 and this) shr 6
    val newBit2 = (count2 or previousBit2) xor (0b11)

    val count3 = (0b0001_0011_0101_0111 and this).countOneBits()
    val previousBit3 = (0b0000_0000_0000_1000 and this) shr 3
    val newBit3 = (count3 or previousBit3) xor (0b11)

    return (-((-newBit0 ushr 31) xor 0b1) and 0b1000) or
        (-((-newBit1 ushr 31) xor 0b1) and 0b0100) or
        (-((-newBit2 ushr 31) xor 0b1) and 0b0010) or
        (-((-newBit3 ushr 31) xor 0b1) and 0b0001)
}

/**
 * A 64 KB lookup table mapping any 16-bit 4x4 grid in Morton order to its next generation 2x2 center (4 bits).
 *
 * This precomputes Conway's Game of Life transition rule for all 65,536 possible 4x4 neighborhood states,
 * replacing runtime neighbor counting and bitwise branching with a single L1 data cache array load.
 */
private val NEXT_GEN_4X4_LUT = ByteArray(65536) { it.computeNextGeneration().toByte() }

/**
 * A 256 KB lookup table indexed by a 16-bit 4x4 quadrant (`0..65535`) in Morton order.
 *
 * Pre-extracts and packs the sub-components of the quadrant into a single 32-bit [Int] to accelerate assembling
 * the four overlapping 4x4 subnodes (`subNW`, `subNE`, `subSW`, `subSE`) needed by [computeLeafNextGeneration]:
 * - Bits 0..3: `center` (2x2 center cells of the quadrant).
 * - Bits 4..7: `right` (vertical edge cells at the right border of the quadrant, aligned for horizontal neighbors).
 * - Bits 8..11: `left` (vertical edge cells at the left border of the quadrant, aligned for horizontal neighbors).
 * - Bits 12..15: `bottom` (horizontal edge cells at the bottom border of the quadrant, aligned for vertical neighbors).
 * - Bits 16..19: `top` (horizontal edge cells at the top border of the quadrant, aligned for vertical neighbors).
 * - Bits 20..23: `corner` (corner cells needed by the diagonally adjacent quadrant).
 *
 * Looking up each quadrant in this table replaces over 40 individual bit shifts and masks with 4 array loads.
 */
private val QUAD_INFO_LUT = IntArray(65536) { q ->
    val c = q ushr 3
    val center = (c and 1) or ((c ushr 2) and 2) or ((c ushr 4) and 4) or ((c ushr 6) and 8)
    val right = ((q ushr 7) and 1) or (((q ushr 13) and 1) shl 2)
    val left = (((q ushr 2) and 1) shl 1) or (((q ushr 8) and 1) shl 3)
    val bottom = ((q ushr 11) and 1) or (((q ushr 14) and 1) shl 1)
    val top = (((q ushr 1) and 1) shl 2) or (((q ushr 4) and 1) shl 3)
    val corner = ((q ushr 15) and 1) or (((q ushr 10) and 1) shl 1) or (((q ushr 5) and 1) shl 2) or ((q and 1) shl 3)

    center or (right shl 4) or (left shl 8) or (bottom shl 12) or (top shl 16) or (corner shl 20)
}

/**
 * Computes the 4x4 [Int] next generation for the given 8x8 64-bit Morton leaf node in its center.
 */
fun Long.computeLeafNextGeneration(): Int {
    if (this == 0L) return 0

    val q0 = (this and 0xFFFFL).toInt()
    val q1 = ((this ushr 16) and 0xFFFFL).toInt()
    val q2 = ((this ushr 32) and 0xFFFFL).toInt()
    val q3 = (this ushr 48).toInt()

    val quadLut = QUAD_INFO_LUT
    val info0 = quadLut[q0]
    val info1 = quadLut[q1]
    val info2 = quadLut[q2]
    val info3 = quadLut[q3]

    val n00 = info0 and 0xF
    val n02 = info1 and 0xF
    val n20 = info2 and 0xF
    val n22 = info3 and 0xF

    val n01 = ((info0 ushr 4) and 0x5) or ((info1 ushr 8) and 0xA)
    val n21 = ((info2 ushr 4) and 0x5) or ((info3 ushr 8) and 0xA)

    val n10 = ((info0 ushr 12) and 0x3) or ((info2 ushr 16) and 0xC)
    val n12 = ((info1 ushr 12) and 0x3) or ((info3 ushr 16) and 0xC)

    val n11 = ((info0 ushr 20) and 1) or
        ((info1 ushr 20) and 2) or
        ((info2 ushr 20) and 4) or
        ((info3 ushr 20) and 8)

    val lut = NEXT_GEN_4X4_LUT
    val nw = lut[n00 or (n01 shl 4) or (n10 shl 8) or (n11 shl 12)].toInt()
    val ne = lut[n01 or (n02 shl 4) or (n11 shl 8) or (n12 shl 12)].toInt()
    val sw = lut[n10 or (n11 shl 4) or (n20 shl 8) or (n21 shl 12)].toInt()
    val se = lut[n11 or (n12 shl 4) or (n21 shl 8) or (n22 shl 12)].toInt()

    return nw or (ne shl 4) or (sw shl 8) or (se shl 12)
}

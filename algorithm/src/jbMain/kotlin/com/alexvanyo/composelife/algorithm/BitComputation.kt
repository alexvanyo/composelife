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
 * Computes the 4x4 [Int] next generation for the given 8x8 [MacroCell.LeafNode] in its center.
 *
 * TODO: Fully inline this, to avoid as much shifting as possible.
 */
internal fun MacroCell.LeafNode.computeNextGeneration(): Int {
    val n00 = ((this and (1L shl 0x03)) ushr (0x03)) or
        ((this and (1L shl 0x06)) ushr (0x06 - 1)) or
        ((this and (1L shl 0x09)) ushr (0x09 - 2)) or
        ((this and (1L shl 0x0C)) ushr (0x0C - 3))
    val n01 = ((this and (1L shl 0x07)) ushr (0x07)) or
        ((this and (1L shl 0x12)) ushr (0x12 - 1)) or
        ((this and (1L shl 0x0D)) ushr (0x0D - 2)) or
        ((this and (1L shl 0x18)) ushr (0x18 - 3))
    val n02 = ((this and (1L shl 0x13)) ushr (0x13)) or
        ((this and (1L shl 0x16)) ushr (0x16 - 1)) or
        ((this and (1L shl 0x19)) ushr (0x19 - 2)) or
        ((this and (1L shl 0x1C)) ushr (0x1C - 3))
    val n10 = ((this and (1L shl 0x0B)) ushr (0x0B)) or
        ((this and (1L shl 0x0E)) ushr (0x0E - 1)) or
        ((this and (1L shl 0x21)) ushr (0x21 - 2)) or
        ((this and (1L shl 0x24)) ushr (0x24 - 3))
    val n11 = ((this and (1L shl 0x0F)) ushr (0x0F)) or
        ((this and (1L shl 0x1A)) ushr (0x1A - 1)) or
        ((this and (1L shl 0x25)) ushr (0x25 - 2)) or
        ((this and (1L shl 0x30)) ushr (0x30 - 3))
    val n12 = ((this and (1L shl 0x1B)) ushr (0x1B)) or
        ((this and (1L shl 0x1E)) ushr (0x1E - 1)) or
        ((this and (1L shl 0x31)) ushr (0x31 - 2)) or
        ((this and (1L shl 0x34)) ushr (0x34 - 3))
    val n20 = ((this and (1L shl 0x23)) ushr (0x23)) or
        ((this and (1L shl 0x26)) ushr (0x26 - 1)) or
        ((this and (1L shl 0x29)) ushr (0x29 - 2)) or
        ((this and (1L shl 0x2C)) ushr (0x2C - 3))
    val n21 = ((this and (1L shl 0x27)) ushr (0x27)) or
        ((this and (1L shl 0x32)) ushr (0x32 - 1)) or
        ((this and (1L shl 0x2D)) ushr (0x2D - 2)) or
        ((this and (1L shl 0x38)) ushr (0x38 - 3))
    val n22 = ((this and (1L shl 0x33)) ushr (0x33)) or
        ((this and (1L shl 0x36)) ushr (0x36 - 1)) or
        ((this and (1L shl 0x39)) ushr (0x39 - 2)) or
        ((this and (1L shl 0x3C)) ushr (0x3C - 3))

    val nw = (n00 or (n01 shl 4) or (n10 shl 8) or (n11 shl 12)).toInt().computeNextGeneration()
    val ne = (n01 or (n02 shl 4) or (n11 shl 8) or (n12 shl 12)).toInt().computeNextGeneration()
    val sw = (n10 or (n11 shl 4) or (n20 shl 8) or (n21 shl 12)).toInt().computeNextGeneration()
    val se = (n11 or (n12 shl 4) or (n21 shl 8) or (n22 shl 12)).toInt().computeNextGeneration()

    return nw or (ne shl 4) or (sw shl 8) or (se shl 12)
}

@Suppress("NOTHING_TO_INLINE")
internal inline fun Int.computeNextGeneration(): Int {
    val count0 = (0b1110_1010_1100_1000 and this).bitCount()
    val previousBit0 = (0b0001_0000_0000_0000 and this) shr 12
    val newBit0 = (count0 or previousBit0) xor (0b11)

    val count1 = (0b0101_1101_0100_1100 and this).bitCount()
    val previousBit1 = (0b0000_0010_0000_0000 and this) shr 9
    val newBit1 = (count1 or previousBit1) xor (0b11)

    val count2 = (0b0011_0010_1011_1010 and this).bitCount()
    val previousBit2 = (0b0000_0000_0100_0000 and this) shr 6
    val newBit2 = (count2 or previousBit2) xor (0b11)

    val count3 = (0b0001_0011_0101_0111 and this).bitCount()
    val previousBit3 = (0b0000_0000_0000_1000 and this) shr 3
    val newBit3 = (count3 or previousBit3) xor (0b11)

    return (-((-newBit0 ushr 31) xor 0b1) and 0b1000) or
        (-((-newBit1 ushr 31) xor 0b1) and 0b0100) or
        (-((-newBit2 ushr 31) xor 0b1) and 0b0010) or
        (-((-newBit3 ushr 31) xor 0b1) and 0b0001)
}

@Suppress("NOTHING_TO_INLINE")
private inline fun Int.bitCount(): Int {
    val a = this - ((this ushr 1) and 0x55555555)
    val b = (a and 0x33333333) + ((a ushr 2) and 0x33333333)
    val c = (b + (b ushr 4)) and 0x0f0f0f0f
    val d = c + (c ushr 8)
    val e = d + (d ushr 16)
    return e and 0x3f
}

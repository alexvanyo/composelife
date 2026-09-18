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

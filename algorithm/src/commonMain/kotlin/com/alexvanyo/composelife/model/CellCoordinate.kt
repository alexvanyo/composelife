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

import kotlin.jvm.JvmInline

/**
 * A lightweight 2D integer cell coordinate for Game of Life cells.
 *
 * Packed as two 32-bit integers in a 64-bit [Long] for zero-allocation performance.
 */
@JvmInline
value class CellCoordinate(val packedValue: Long) {
    constructor(x: Int, y: Int) : this((x.toLong() shl 32) or (y.toLong() and 0xFFFFFFFFL))

    val x: Int get() = (packedValue shr 32).toInt()
    val y: Int get() = (packedValue and 0xFFFFFFFFL).toInt()

    operator fun component1(): Int = x
    operator fun component2(): Int = y

    override fun toString(): String = "($x, $y)"
}

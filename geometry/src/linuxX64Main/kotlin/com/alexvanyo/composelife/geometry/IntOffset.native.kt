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

@file:Suppress("EXPECT_ACTUAL_CLASSIFIERS_ARE_IN_BETA_WARNING")

package com.alexvanyo.composelife.geometry

actual value class IntOffset(actual val packedValue: Long) {
    actual val x: Int get() = (packedValue shr 32).toInt()
    actual val y: Int get() = (packedValue and 0xFFFFFFFFL).toInt()

    actual operator fun component1(): Int = x
    actual operator fun component2(): Int = y

    actual operator fun minus(other: IntOffset): IntOffset = IntOffset(x - other.x, y - other.y)
    actual operator fun plus(other: IntOffset): IntOffset = IntOffset(x + other.x, y + other.y)
}

actual fun IntOffset(x: Int, y: Int): IntOffset = IntOffset(
    (x.toLong() shl 32) or (y.toLong() and 0xFFFFFFFFL),
)

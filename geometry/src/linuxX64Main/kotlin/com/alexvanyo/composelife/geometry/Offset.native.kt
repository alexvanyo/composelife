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

import kotlin.math.sqrt

actual value class Offset(actual val packedValue: Long) {
    actual val x: Float get() = Float.fromBits((packedValue shr 32).toInt())
    actual val y: Float get() = Float.fromBits((packedValue and 0xFFFFFFFFL).toInt())

    actual operator fun component1(): Float = x
    actual operator fun component2(): Float = y

    actual operator fun minus(other: Offset): Offset = Offset(x - other.x, y - other.y)
    actual operator fun plus(other: Offset): Offset = Offset(x + other.x, y + other.y)
    actual operator fun div(operand: Float): Offset = Offset(x / operand, y / operand)
    actual fun getDistance(): Float = sqrt(x * x + y * y)
}

actual fun Offset(x: Float, y: Float): Offset = Offset(
    (x.toRawBits().toLong() shl 32) or (y.toRawBits().toLong() and 0xFFFFFFFFL),
)

actual fun lerp(start: Offset, stop: Offset, fraction: Float): Offset = Offset(
    start.x + (stop.x - start.x) * fraction,
    start.y + (stop.y - start.y) * fraction,
)

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

import kotlin.jvm.JvmInline

@JvmInline
expect value class Offset(val packedValue: Long) {
    val x: Float
    val y: Float

    operator fun component1(): Float
    operator fun component2(): Float

    operator fun minus(other: Offset): Offset
    operator fun plus(other: Offset): Offset
    operator fun div(operand: Float): Offset
    fun getDistance(): Float
}

expect fun Offset(x: Float, y: Float): Offset

expect fun lerp(start: Offset, stop: Offset, fraction: Float): Offset

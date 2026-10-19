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
 * Thrown by [FlatLeanHashLifeAlgorithm] when a pattern cannot be represented by a [FlatHashLifeArena]: either it
 * does not fit in an arena of the maximum capacity, or its next generation leaves the 32-bit coordinate range
 * supported by the flat engine.
 *
 * This deliberately does not extend [IllegalStateException], so that callers falling back to another algorithm
 * on this failure never swallow coroutine cancellation.
 */
class FlatHashLifeArenaException(message: String) : RuntimeException(message)

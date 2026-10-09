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

import com.alexvanyo.composelife.geometry.IntOffset
import com.alexvanyo.composelife.geometry.getMooreNeighbors

/**
 * Pure function computing one generation of Conway's Game of Life on a set of [IntOffset]s.
 */
fun stepGeneration(aliveCells: Set<IntOffset>): Set<IntOffset> {
    val candidates = aliveCells.flatMapTo(mutableSetOf(), IntOffset::getMooreNeighbors)
    candidates.addAll(aliveCells)
    return candidates.filterTo(mutableSetOf()) { cell ->
        val neighborCount = cell.getMooreNeighbors().count { it in aliveCells }
        neighborCount == 3 || (neighborCount == 2 && cell in aliveCells)
    }
}

/**
 * Pure function computing [step] generations of Conway's Game of Life.
 */
tailrec fun stepGenerations(aliveCells: Set<IntOffset>, step: Int): Set<IntOffset> = if (step <= 0) {
    aliveCells
} else {
    stepGenerations(stepGeneration(aliveCells), step - 1)
}

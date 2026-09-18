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

import com.alexvanyo.composelife.model.CellCoordinate

/**
 * Returns the 8 Moore neighbors of this [CellCoordinate].
 */
fun CellCoordinate.getMooreNeighbors(): Set<CellCoordinate> {
    val cx = x
    val cy = y
    return setOf(
        CellCoordinate(cx - 1, cy - 1),
        CellCoordinate(cx, cy - 1),
        CellCoordinate(cx + 1, cy - 1),
        CellCoordinate(cx - 1, cy),
        CellCoordinate(cx + 1, cy),
        CellCoordinate(cx - 1, cy + 1),
        CellCoordinate(cx, cy + 1),
        CellCoordinate(cx + 1, cy + 1),
    )
}

/**
 * Pure function computing one generation of Conway's Game of Life on a set of [CellCoordinate]s.
 */
fun stepGeneration(aliveCells: Set<CellCoordinate>): Set<CellCoordinate> {
    val candidates = aliveCells.flatMapTo(mutableSetOf(), CellCoordinate::getMooreNeighbors)
    candidates.addAll(aliveCells)
    return candidates.filterTo(mutableSetOf()) { cell ->
        val neighborCount = cell.getMooreNeighbors().count { it in aliveCells }
        neighborCount == 3 || (neighborCount == 2 && cell in aliveCells)
    }
}

/**
 * Pure function computing [step] generations of Conway's Game of Life.
 */
tailrec fun stepGenerations(aliveCells: Set<CellCoordinate>, step: Int): Set<CellCoordinate> = if (step <= 0) {
    aliveCells
} else {
    stepGenerations(stepGeneration(aliveCells), step - 1)
}

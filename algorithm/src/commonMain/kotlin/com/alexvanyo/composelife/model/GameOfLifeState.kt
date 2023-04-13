/*
 * Copyright 2022 The Android Open Source Project
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

import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset

/**
 * The state describing a particular game of life pattern given by the [CellState].
 */
@Stable
interface GameOfLifeState {
    val cellState: CellState
}

/**
 * A simple implementation of an immutable [GameOfLifeState].
 */
private class ImmutableGameOfLifeState(
    override val cellState: CellState,
) : GameOfLifeState

/**
 * Creates a fixed [GameOfLifeState] for the given [cellState].
 */
fun GameOfLifeState(cellState: CellState): GameOfLifeState = ImmutableGameOfLifeState(cellState)

/**
 * A mutable [GameOfLifeState] where [cellState] can be modified.
 */
interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: CellState
}

/**
 * Creates a [MutableGameOfLifeState] with the given initial [cellState]/
 */
fun MutableGameOfLifeState(cellState: CellState): MutableGameOfLifeState = MutableGameOfLifeStateImpl(cellState)

/**
 * A simple implementation of a mutable [GameOfLifeState].
 */
private class MutableGameOfLifeStateImpl(
    cellState: CellState,
) : MutableGameOfLifeState {
    override var cellState by mutableStateOf(cellState)
}

/**
 * Modifies the given [MutableGameOfLifeState] by setting the cell state at the given [cellCoordinate] to [isAlive].
 */
fun MutableGameOfLifeState.setCellState(cellCoordinate: IntOffset, isAlive: Boolean) {
    cellState = cellState.withCell(cellCoordinate, isAlive)
}

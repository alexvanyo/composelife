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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset

interface GameOfLifeState {
    val cellState: CellState
}

private class ImmutableGameOfLifeState(
    override val cellState: CellState,
) : GameOfLifeState

fun GameOfLifeState(cellState: CellState): GameOfLifeState = ImmutableGameOfLifeState(cellState)

interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: CellState
}

fun MutableGameOfLifeState(cellState: CellState): MutableGameOfLifeState = MutableGameOfLifeStateImpl(cellState)

private class MutableGameOfLifeStateImpl(
    cellState: CellState,
) : MutableGameOfLifeState {
    override var cellState by mutableStateOf(cellState)
}

fun MutableGameOfLifeState.setCellState(cellCoordinate: IntOffset, isAlive: Boolean) {
    cellState = cellState.withCell(cellCoordinate, isAlive)
}

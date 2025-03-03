/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import com.slack.circuit.retained.rememberRetained
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.conflate
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.transform
import kotlin.time.Duration.Companion.seconds

interface CellUniversePaneInjectEntryPoint :
    CellStateRepositoryProvider,
    GameOfLifeAlgorithmProvider,
    ClockProvider,
    ComposeLifeDispatchersProvider,
    GameOfLifeProgressIndicatorInjectEntryPoint,
    InteractiveCellUniverseInjectEntryPoint

interface CellUniversePaneLocalEntryPoint :
    GameOfLifeProgressIndicatorLocalEntryPoint,
    InteractiveCellUniverseLocalEntryPoint

context(CellStateRepositoryProvider, GameOfLifeAlgorithmProvider, ComposeLifeDispatchersProvider, ClockProvider)
@Suppress("LongMethod")
@Composable
fun rememberCellUniversePaneState(): CellUniversePaneState {
    var retainedInitialSaveableCellState: SaveableCellState? by rememberRetained { mutableStateOf(null) }
    var retainedTemporalGameOfLifeState: TemporalGameOfLifeState? by rememberRetained { mutableStateOf(null) }

    val initialSaveableCellState = retainedInitialSaveableCellState
    val temporalGameOfLifeState = retainedTemporalGameOfLifeState

    if (initialSaveableCellState == null) {
        LaunchedEffect(cellStateRepository) {
            val newInitialSaveableCellState = cellStateRepository.getAutosavedCellState()
                ?: SaveableCellState(
                    gosperGliderGun,
                    CellStateMetadata(null, null, null, 0, false),
                )

            retainedInitialSaveableCellState = newInitialSaveableCellState
            retainedTemporalGameOfLifeState = TemporalGameOfLifeState(
                seedCellState = newInitialSaveableCellState.cellState,
                isRunning = false,
            )
        }
    }

    return if (initialSaveableCellState == null || temporalGameOfLifeState == null) {
        CellUniversePaneState.LoadingCellState
    } else {
        val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
            temporalGameOfLifeState = temporalGameOfLifeState,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
            dispatchers = dispatchers,
            clock = clock,
        )

        LaunchedEffect(temporalGameOfLifeStateMutator) {
            temporalGameOfLifeStateMutator.update()
        }

        var cellStateMetadataId by remember {
            mutableStateOf(initialSaveableCellState.cellStateMetadata.id)
        }

        LaunchedEffect(temporalGameOfLifeState) {
            snapshotFlow { temporalGameOfLifeState.cellState }
                .conflate()
                .transform {
                    emit(it)
                    delay(5.seconds)
                }
                .onEach { cellState ->
                    cellStateMetadataId = cellStateRepository.autosaveCellState(
                        saveableCellState = SaveableCellState(
                            cellState = cellState,
                            cellStateMetadata = CellStateMetadata(
                                id = cellStateMetadataId,
                                name = initialSaveableCellState.cellStateMetadata.name,
                                description = initialSaveableCellState
                                    .cellStateMetadata
                                    .description,
                                generation = initialSaveableCellState
                                    .cellStateMetadata
                                    .generation,
                                wasAutosaved = initialSaveableCellState
                                    .cellStateMetadata
                                    .wasAutosaved,
                            ),
                        ),
                    )
                }
                .collect()
        }

        remember(temporalGameOfLifeState) {
            object : CellUniversePaneState.LoadedCellState {
                override val temporalGameOfLifeState: TemporalGameOfLifeState = temporalGameOfLifeState
            }
        }
    }
}

sealed interface CellUniversePaneState {
    /**
     * The initial cell state is loading
     */
    data object LoadingCellState : CellUniversePaneState

    /**
     * The cell state is loaded
     */
    interface LoadedCellState : CellUniversePaneState {
        val temporalGameOfLifeState: TemporalGameOfLifeState
    }
}

internal val gosperGliderGun = """
    |........................O...........
    |......................O.O...........
    |............OO......OO............OO
    |...........O...O....OO............OO
    |OO........O.....O...OO..............
    |OO........O...O.OO....O.O...........
    |..........O.....O.......O...........
    |...........O...O....................
    |............OO......................
""".toCellState()

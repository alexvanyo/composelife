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

package com.alexvanyo.composelife.algorithm

import androidx.compose.runtime.snapshotFlow
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.algorithmChoiceState
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.resourcestate.map
import com.alexvanyo.composelife.resourcestate.successes
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.channelFlow
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.produceIn
import kotlinx.coroutines.isActive
import kotlinx.coroutines.selects.select

@Inject
@ContributesBinding(AppScope::class)
class ConfigurableGameOfLifeAlgorithm(
    private val preferences: ComposeLifePreferences,
    private val naiveGameOfLifeAlgorithm: NaiveGameOfLifeAlgorithm,
    private val hashLifeAlgorithm: HashLifeAlgorithm,
) : GameOfLifeAlgorithm {

    private val currentAlgorithm get() = preferences.algorithmChoiceState.map { algorithmType ->
        when (algorithmType) {
            AlgorithmType.NaiveAlgorithm -> naiveGameOfLifeAlgorithm
            AlgorithmType.HashLifeAlgorithm -> hashLifeAlgorithm
        }
    }

    override suspend fun computeGenerationWithStep(cellState: CellState, step: Int): CellState =
        snapshotFlow { currentAlgorithm }.firstSuccess().value.computeGenerationWithStep(
            cellState = cellState,
            step = step,
        )

    override fun computeGenerationsWithStep(originalCellState: CellState, step: Int): Flow<CellState> =
        channelFlow {
            // Start listening to algorithm changes
            val algorithmChannel = snapshotFlow { currentAlgorithm }
                .successes()
                .map { it.value }
                .buffer(Channel.CONFLATED) // We only care about the current algorithm
                .produceIn(this)

            // Setup a receive channel for
            var cellStateChannel: ReceiveChannel<CellState>? = null
            var cellState = originalCellState

            while (currentCoroutineContext().isActive) {
                // Select between a new cell state being produced and a new algorithm update coming through
                // select guarantees that we'll either send a new state, or switch algorithms with the most recently
                // emitted cell state
                select<Unit> {
                    // Bias towards updating the algorithm, it's expected that there will always be a new cell state
                    // available.
                    algorithmChannel.onReceive {
                        // Cancel the ongoing cell state production with the old algorithm, if any
                        cellStateChannel?.cancel()
                        cellStateChannel = it.computeGenerationsWithStep(
                            originalCellState = cellState,
                            step = step,
                        )
                            .buffer(Channel.RENDEZVOUS) // Buffer rendezvous, we'll only compute what we need by default
                            .produceIn(this@channelFlow)
                    }
                    cellStateChannel?.onReceive { newCellState ->
                        cellState = newCellState
                        send(newCellState)
                    }
                }
            }
        }
            .buffer(Channel.RENDEZVOUS) // Buffer rendezvous, we'll only compute what we need by default
}

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

package com.alexvanyo.composelife.wear

import android.view.SurfaceHolder
import androidx.compose.runtime.snapshots.Snapshot
import androidx.compose.ui.platform.AndroidUiDispatcher
import androidx.wear.watchface.ComplicationSlotsManager
import androidx.wear.watchface.WatchFace
import androidx.wear.watchface.WatchFaceService
import androidx.wear.watchface.WatchFaceType
import androidx.wear.watchface.WatchState
import androidx.wear.watchface.style.CurrentUserStyleRepository
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.emptyCellState
import dagger.hilt.android.AndroidEntryPoint
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import kotlinx.datetime.Clock
import javax.inject.Inject

@AndroidEntryPoint(WatchFaceService::class)
class GameOfLifeWatchFaceService : Hilt_GameOfLifeWatchFaceService() {

    @Inject
    lateinit var gameOfLifeAlgorithm: GameOfLifeAlgorithm

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    private val scope = CoroutineScope(SupervisorJob() + AndroidUiDispatcher.Main)

    private val temporalGameOfLifeState = TemporalGameOfLifeState(
        cellState = emptyCellState(),
        isRunning = false,
        targetStepsPerSecond = 20.0,
    )

    override fun onCreate() {
        super.onCreate()
        scope.launch {
            temporalGameOfLifeState.evolve(
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = Clock.System,
                dispatchers = dispatchers,
            )
        }
    }

    override suspend fun createWatchFace(
        surfaceHolder: SurfaceHolder,
        watchState: WatchState,
        complicationSlotsManager: ComplicationSlotsManager,
        currentUserStyleRepository: CurrentUserStyleRepository,
    ): WatchFace {
        watchState.isAmbient
            .onEach {
                if (it == true) {
                    Snapshot.withMutableSnapshot {
                        temporalGameOfLifeState.cellState = temporalGameOfLifeState.seedCellState
                    }
                }
            }
            .launchIn(scope)

        combine(
            watchState.isVisible,
            watchState.isAmbient,
        ) { isVisible, isAmbient ->
            Snapshot.withMutableSnapshot {
                temporalGameOfLifeState.setIsRunning(isVisible == true && isAmbient == false)
            }
        }
            .launchIn(scope)

        return WatchFace(
            watchFaceType = WatchFaceType.DIGITAL,
            renderer = GameOfLifeRenderer(
                context = this,
                surfaceHolder = surfaceHolder,
                currentUserStyleRepository = currentUserStyleRepository,
                watchState = watchState,
                temporalGameOfLifeState = temporalGameOfLifeState,
            ),
        )
    }

    override fun onDestroy() {
        super.onDestroy()
        scope.cancel()
    }
}

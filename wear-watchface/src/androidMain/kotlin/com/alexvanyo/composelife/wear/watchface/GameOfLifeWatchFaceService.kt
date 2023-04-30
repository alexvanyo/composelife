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

package com.alexvanyo.composelife.wear.watchface

import android.util.Log
import android.view.SurfaceHolder
import androidx.compose.runtime.snapshots.Snapshot
import androidx.compose.ui.graphics.toArgb
import androidx.compose.ui.platform.AndroidUiDispatcher
import androidx.wear.watchface.ComplicationSlot
import androidx.wear.watchface.ComplicationSlotsManager
import androidx.wear.watchface.TapEvent
import androidx.wear.watchface.TapType
import androidx.wear.watchface.WatchFace
import androidx.wear.watchface.WatchFaceColors
import androidx.wear.watchface.WatchFaceExperimental
import androidx.wear.watchface.WatchFaceService
import androidx.wear.watchface.WatchFaceType
import androidx.wear.watchface.WatchState
import androidx.wear.watchface.style.CurrentUserStyleRepository
import androidx.wear.watchface.style.UserStyleSchema
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.wear.watchface.configuration.createGameOfLifeComplicationSlotsManager
import com.alexvanyo.composelife.wear.watchface.configuration.createGameOfLifeStyleSchema
import com.alexvanyo.composelife.wear.watchface.configuration.getGameOfLifeColor
import dagger.hilt.android.AndroidEntryPoint
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import kotlinx.coroutines.cancel
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.flow.launchIn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import kotlinx.datetime.Clock
import javax.inject.Inject

@OptIn(WatchFaceExperimental::class)
@AndroidEntryPoint(WatchFaceService::class)
class GameOfLifeWatchFaceService : Hilt_GameOfLifeWatchFaceService() {

    @Inject
    lateinit var gameOfLifeAlgorithm: GameOfLifeAlgorithm

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    private val scope = CoroutineScope(SupervisorJob() + AndroidUiDispatcher.Main)

    private val temporalGameOfLifeState = TemporalGameOfLifeState(
        seedCellState = emptyCellState(),
        isRunning = false,
        targetStepsPerSecond = 20.0,
    )

    private val isBeingTappedState = MutableStateFlow(false)

    override fun onCreate() {
        super.onCreate()
        scope.launch {
            with(gameOfLifeAlgorithm) {
                with(dispatchers) {
                    with(Clock.System) {
                        temporalGameOfLifeState.evolve()
                    }
                }
            }
        }
    }

    override fun createUserStyleSchema(): UserStyleSchema = createGameOfLifeStyleSchema(
        context = applicationContext,
    )

    override fun createComplicationSlotsManager(
        currentUserStyleRepository: CurrentUserStyleRepository,
    ): ComplicationSlotsManager = createGameOfLifeComplicationSlotsManager(
        context = applicationContext,
        currentUserStyleRepository = currentUserStyleRepository,
    )

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

        val renderer = GameOfLifeRenderer(
            context = this,
            surfaceHolder = surfaceHolder,
            currentUserStyleRepository = currentUserStyleRepository,
            complicationSlotsManager = complicationSlotsManager,
            watchState = watchState,
            temporalGameOfLifeState = temporalGameOfLifeState,
        )

        combine(
            watchState.isVisible,
            watchState.isAmbient,
            isBeingTappedState,
        ) { isVisible, isAmbient, isBeingTapped ->
            val isRunning = isVisible == true && isAmbient == false && !isBeingTapped
            Log.d("vanyo", "isRunning: $isRunning")
            renderer.interactiveDrawModeUpdateDelayMillis = if (isRunning) 50 else 1000
            Snapshot.withMutableSnapshot {
                temporalGameOfLifeState.setIsRunning(isRunning)
            }
        }
            .launchIn(scope)

        currentUserStyleRepository.userStyle
            .onEach { userStyle ->
                val color = with(currentUserStyleRepository.schema) {
                    android.graphics.Color.valueOf(userStyle.getGameOfLifeColor().toArgb())
                }
                renderer.watchfaceColors = WatchFaceColors(
                    primaryColor = color,
                    secondaryColor = color,
                    tertiaryColor = color,
                )
            }
            .launchIn(scope)

        return WatchFace(
            watchFaceType = @Suppress("RestrictedApi") WatchFaceType.DIGITAL,
            renderer = renderer,
        ).apply {
            setTapListener(
                object : WatchFace.TapListener {
                    @Suppress("RestrictedApi")
                    override fun onTapEvent(tapType: Int, tapEvent: TapEvent, complicationSlot: ComplicationSlot?) {
                        when (tapType) {
                            TapType.DOWN -> {
                                temporalGameOfLifeState.cellState = temporalGameOfLifeState.seedCellState
                                isBeingTappedState.value = true
                            }
                            else -> {
                                isBeingTappedState.value = false
                            }
                        }
                    }
                },
            )
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        scope.cancel()
    }
}

package com.alexvanyo.composelife.wear

import android.view.SurfaceHolder
import androidx.compose.runtime.snapshots.Snapshot
import androidx.compose.ui.platform.AndroidUiDispatcher
import androidx.wear.watchface.ComplicationSlot
import androidx.wear.watchface.ComplicationSlotsManager
import androidx.wear.watchface.TapEvent
import androidx.wear.watchface.TapType
import androidx.wear.watchface.WatchFace
import androidx.wear.watchface.WatchFaceService
import androidx.wear.watchface.WatchFaceType
import androidx.wear.watchface.WatchState
import androidx.wear.watchface.style.CurrentUserStyleRepository
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.emptyCellState
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

@AndroidEntryPoint(WatchFaceService::class)
class GameOfLifeWatchFaceService : Hilt_GameOfLifeWatchFaceService() {

    @Inject
    lateinit var gameOfLifeAlgorithm: GameOfLifeAlgorithm

    private val scope = CoroutineScope(SupervisorJob() + AndroidUiDispatcher.Main)

    private val temporalGameOfLifeState = TemporalGameOfLifeState(
        cellState = emptyCellState(),
        isRunning = false,
        targetStepsPerSecond = 5.0
    )

    private val isBeingTappedState = MutableStateFlow(false)

    override fun onCreate() {
        super.onCreate()
        scope.launch {
            temporalGameOfLifeState.evolve(
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = Clock.System
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
                    temporalGameOfLifeState.cellState = temporalGameOfLifeState.seedCellState
                    Snapshot.sendApplyNotifications()
                }
            }
            .launchIn(scope)

        combine(
            watchState.isVisible,
            watchState.isAmbient,
            isBeingTappedState
        ) { isVisible, isAmbient, isBeingTapped ->
            temporalGameOfLifeState.setIsRunning(isVisible == true && isAmbient == false && !isBeingTapped)
            Snapshot.sendApplyNotifications()
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
            )
        ).apply {
            setTapListener(
                object : WatchFace.TapListener {
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
                }
            )
        }
    }

    override fun onDestroy() {
        super.onDestroy()
        scope.cancel()
    }
}

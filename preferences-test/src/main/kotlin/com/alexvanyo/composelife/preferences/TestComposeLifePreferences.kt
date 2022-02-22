package com.alexvanyo.composelife.preferences

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.runtime.snapshots.Snapshot
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.combine
import com.alexvanyo.composelife.resourcestate.firstSuccess
import javax.inject.Inject

class TestComposeLifePreferences @Inject constructor() : ComposeLifePreferences {
    override var algorithmChoiceState: ResourceState<AlgorithmType> by mutableStateOf(ResourceState.Loading)
        private set

    private var currentShapeType: ResourceState<CurrentShapeType> by mutableStateOf(ResourceState.Loading)

    private var roundRectangleConfig:
        ResourceState<CurrentShape.RoundRectangle> by mutableStateOf(ResourceState.Loading)

    override val currentShapeState: ResourceState<CurrentShape> get() =
        combine(
            currentShapeType,
            roundRectangleConfig
        ) { currentShapeType, roundRectangleConfig ->
            when (currentShapeType) {
                CurrentShapeType.RoundRectangle -> roundRectangleConfig
            }
        }

    override suspend fun setAlgorithmChoice(algorithm: AlgorithmType) {
        Snapshot.withMutableSnapshot {
            algorithmChoiceState = ResourceState.Success(algorithm)
        }
    }

    override suspend fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
        Snapshot.withMutableSnapshot {
            this.currentShapeType = ResourceState.Success(currentShapeType)
        }
    }

    override suspend fun setRoundRectangleConfig(update: (CurrentShape.RoundRectangle) -> CurrentShape.RoundRectangle) {
        val oldRoundRectangleConfig = snapshotFlow { roundRectangleConfig }.firstSuccess().value
        Snapshot.withMutableSnapshot {
            roundRectangleConfig = ResourceState.Success(update(oldRoundRectangleConfig))
        }
    }

    fun setRoundRectangleConfig(roundRectangle: CurrentShape.RoundRectangle) {
        Snapshot.withMutableSnapshot {
            roundRectangleConfig = ResourceState.Success(roundRectangle)
        }
    }
}

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
            roundRectangleConfig,
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

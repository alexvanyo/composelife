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
import kotlinx.coroutines.awaitCancellation

@Suppress("TooManyFunctions")
class TestComposeLifePreferences : ComposeLifePreferences {
    override var quickAccessSettingsState:
        ResourceState<Set<QuickAccessSetting>> by mutableStateOf(ResourceState.Loading)
        private set

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

    override var darkThemeConfigState: ResourceState<DarkThemeConfig> by mutableStateOf(ResourceState.Loading)
        private set

    override var disableAGSLState: ResourceState<Boolean> by mutableStateOf(ResourceState.Loading)
        private set

    override var disableOpenGLState: ResourceState<Boolean> by mutableStateOf(ResourceState.Loading)
        private set

    override var doNotKeepProcessState: ResourceState<Boolean> by mutableStateOf(ResourceState.Loading)
        private set

    override val loadedPreferencesState: ResourceState<LoadedComposeLifePreferences>
        get() = combine(
            quickAccessSettingsState,
            algorithmChoiceState,
            currentShapeState,
            darkThemeConfigState,
            disableAGSLState,
            disableOpenGLState,
            doNotKeepProcessState,
        ) {
            @Suppress("UNCHECKED_CAST")
            LoadedComposeLifePreferences(
                quickAccessSettings = it[0] as Set<QuickAccessSetting>,
                algorithmChoice = it[1] as AlgorithmType,
                currentShape = it[2] as CurrentShape,
                darkThemeConfig = it[3] as DarkThemeConfig,
                disableAGSL = it[4] as Boolean,
                disableOpenGL = it[5] as Boolean,
                doNotKeepProcess = it[6] as Boolean,
            )
        }

    override suspend fun update() = awaitCancellation()

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

    override suspend fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
        Snapshot.withMutableSnapshot {
            darkThemeConfigState = ResourceState.Success(darkThemeConfig)
        }
    }

    override suspend fun setRoundRectangleConfig(update: (CurrentShape.RoundRectangle) -> CurrentShape.RoundRectangle) {
        val oldRoundRectangleConfig = snapshotFlow { roundRectangleConfig }.firstSuccess().value
        Snapshot.withMutableSnapshot {
            roundRectangleConfig = ResourceState.Success(update(oldRoundRectangleConfig))
        }
    }

    override suspend fun addQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(true, quickAccessSetting)

    override suspend fun removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(false, quickAccessSetting)

    private suspend fun updateQuickAccessSetting(include: Boolean, quickAccessSetting: QuickAccessSetting) {
        val oldQuickAccessSettings = snapshotFlow { quickAccessSettingsState }.firstSuccess().value

        Snapshot.withMutableSnapshot {
            quickAccessSettingsState = ResourceState.Success(
                if (include) {
                    oldQuickAccessSettings + quickAccessSetting
                } else {
                    oldQuickAccessSettings - quickAccessSetting
                },
            )
        }
    }

    override suspend fun setDisabledAGSL(disabled: Boolean) {
        Snapshot.withMutableSnapshot {
            disableAGSLState = ResourceState.Success(disabled)
        }
    }

    override suspend fun setDisableOpenGL(disabled: Boolean) {
        Snapshot.withMutableSnapshot {
            disableOpenGLState = ResourceState.Success(disabled)
        }
    }

    override suspend fun setDoNotKeepProcess(doNotKeepProcess: Boolean) {
        Snapshot.withMutableSnapshot {
            doNotKeepProcessState = ResourceState.Success(doNotKeepProcess)
        }
    }

    fun testSetAlgorithmChoice(algorithm: AlgorithmType) {
        Snapshot.withMutableSnapshot {
            algorithmChoiceState = ResourceState.Success(algorithm)
        }
    }

    fun testSetCurrentShapeType(currentShapeType: CurrentShapeType) {
        Snapshot.withMutableSnapshot {
            this.currentShapeType = ResourceState.Success(currentShapeType)
        }
    }

    fun testSetDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
        Snapshot.withMutableSnapshot {
            darkThemeConfigState = ResourceState.Success(darkThemeConfig)
        }
    }

    fun testSetRoundRectangleConfig(roundRectangle: CurrentShape.RoundRectangle) {
        Snapshot.withMutableSnapshot {
            roundRectangleConfig = ResourceState.Success(roundRectangle)
        }
    }

    fun testSetQuickAccessSetting(quickAccessSettings: Set<QuickAccessSetting>) {
        Snapshot.withMutableSnapshot {
            this.quickAccessSettingsState = ResourceState.Success(quickAccessSettings)
        }
    }

    fun testSetDisabledAGSL(disabled: Boolean) {
        Snapshot.withMutableSnapshot {
            disableAGSLState = ResourceState.Success(disabled)
        }
    }

    fun testSetDisableOpenGL(disabled: Boolean) {
        Snapshot.withMutableSnapshot {
            disableOpenGLState = ResourceState.Success(disabled)
        }
    }

    fun testSetDoNotKeepProcess(doNotKeepProcess: Boolean) {
        Snapshot.withMutableSnapshot {
            doNotKeepProcessState = ResourceState.Success(doNotKeepProcess)
        }
    }

    companion object {
        @Suppress("LongParameterList")
        fun Loaded(
            algorithmChoice: AlgorithmType = AlgorithmType.NaiveAlgorithm,
            currentShapeType: CurrentShapeType = CurrentShapeType.RoundRectangle,
            roundRectangleConfig: CurrentShape.RoundRectangle = CurrentShape.RoundRectangle(
                sizeFraction = 1.0f,
                cornerFraction = 0.0f,
            ),
            darkThemeConfig: DarkThemeConfig = DarkThemeConfig.FollowSystem,
            quickAccessSettings: Set<QuickAccessSetting> = emptySet(),
            disableAGSL: Boolean = false,
            disableOpenGL: Boolean = false,
            doNotKeepProcess: Boolean = false,
        ) = TestComposeLifePreferences().apply {
            testSetAlgorithmChoice(algorithmChoice)
            testSetCurrentShapeType(currentShapeType)
            testSetRoundRectangleConfig(roundRectangleConfig)
            testSetDarkThemeConfig(darkThemeConfig)
            testSetQuickAccessSetting(quickAccessSettings)
            testSetDisabledAGSL(disableAGSL)
            testSetDisableOpenGL(disableOpenGL)
            testSetDoNotKeepProcess(doNotKeepProcess)
        }
    }
}

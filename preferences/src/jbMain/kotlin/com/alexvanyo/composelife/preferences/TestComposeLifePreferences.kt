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
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.sessionvalue.SessionValue
import kotlinx.datetime.DateTimePeriod
import kotlin.uuid.Uuid

@Suppress("TooManyFunctions", "LongParameterList")
class TestComposeLifePreferences(
    isLoaded: Boolean = true,
    algorithmChoice: AlgorithmType = AlgorithmType.NaiveAlgorithm,
    currentShapeType: CurrentShapeType = CurrentShapeType.RoundRectangle,
    roundRectangleConfig: CurrentShape.RoundRectangle = CurrentShape.RoundRectangle(
        sizeFraction = 1.0f,
        cornerFraction = 0.0f,
    ),
    roundRectangleSessionId: Uuid = Uuid.random(),
    roundRectangleValueId: Uuid = Uuid.random(),
    darkThemeConfig: DarkThemeConfig = DarkThemeConfig.FollowSystem,
    quickAccessSettings: Set<QuickAccessSetting> = emptySet(),
    disableAGSL: Boolean = false,
    disableOpenGL: Boolean = false,
    doNotKeepProcess: Boolean = false,
    touchToolConfig: ToolConfig = ToolConfig.Pan,
    stylusToolConfig: ToolConfig = ToolConfig.Draw,
    mouseToolConfig: ToolConfig = ToolConfig.Draw,
    completedClipboardWatchingOnboarding: Boolean = false,
    enableClipboardWatching: Boolean = false,
    synchronizePatternCollectionsOnMeteredNetwork: Boolean = false,
    patternCollectionsSynchronizationPeriod: DateTimePeriod = DateTimePeriod(hours = 24),
    patternCollectionsSynchronizationPeriodSessionId: Uuid = Uuid.random(),
    patternCollectionsSynchronizationPeriodValueId: Uuid = Uuid.random(),
    enableWindowShapeClipping: Boolean = false,
) : ComposeLifePreferences {
    var quickAccessSettings: Set<QuickAccessSetting> by mutableStateOf(quickAccessSettings)

    var algorithmChoice: AlgorithmType by mutableStateOf(algorithmChoice)

    var currentShapeType: CurrentShapeType by mutableStateOf(currentShapeType)

    var roundRectangleConfig: CurrentShape.RoundRectangle by mutableStateOf(roundRectangleConfig)

    var roundRectangleSessionId: Uuid by mutableStateOf(roundRectangleSessionId)

    var roundRectangleValueId: Uuid by mutableStateOf(roundRectangleValueId)

    var darkThemeConfig: DarkThemeConfig by mutableStateOf(darkThemeConfig)

    var disableAGSL: Boolean by mutableStateOf(disableAGSL)

    var disableOpenGL: Boolean by mutableStateOf(disableOpenGL)

    var doNotKeepProcess: Boolean by mutableStateOf(doNotKeepProcess)

    var touchToolConfig: ToolConfig by mutableStateOf(touchToolConfig)

    var stylusToolConfig: ToolConfig by mutableStateOf(stylusToolConfig)

    var mouseToolConfig: ToolConfig by mutableStateOf(mouseToolConfig)

    var completedClipboardWatchingOnboarding:
        Boolean by mutableStateOf(completedClipboardWatchingOnboarding)

    var enableClipboardWatching:
        Boolean by mutableStateOf(enableClipboardWatching)

    var synchronizePatternCollectionsOnMeteredNetwork:
        Boolean by mutableStateOf(synchronizePatternCollectionsOnMeteredNetwork)

    var patternCollectionsSynchronizationPeriod:
        DateTimePeriod by mutableStateOf(patternCollectionsSynchronizationPeriod)

    var patternCollectionsSynchronizationPeriodSessionId:
        Uuid by mutableStateOf(patternCollectionsSynchronizationPeriodSessionId)

    var patternCollectionsSynchronizationPeriodValueId:
        Uuid by mutableStateOf(patternCollectionsSynchronizationPeriodValueId)

    var enableWindowShapeClipping: Boolean by mutableStateOf(enableWindowShapeClipping)

    var isLoaded by mutableStateOf(isLoaded)

    override val loadedPreferencesState: ResourceState<LoadedComposeLifePreferences>
        get() = if (isLoaded) {
            ResourceState.Success(
                LoadedComposeLifePreferences(
                    quickAccessSettings = quickAccessSettings,
                    algorithmChoice = algorithmChoice,
                    currentShapeType = currentShapeType,
                    roundRectangleSessionValue = SessionValue(
                        sessionId = roundRectangleSessionId,
                        valueId = roundRectangleValueId,
                        value = roundRectangleConfig,
                    ),
                    darkThemeConfig = darkThemeConfig,
                    disableAGSL = disableAGSL,
                    disableOpenGL = disableOpenGL,
                    doNotKeepProcess = doNotKeepProcess,
                    touchToolConfig = touchToolConfig,
                    stylusToolConfig = stylusToolConfig,
                    mouseToolConfig = mouseToolConfig,
                    completedClipboardWatchingOnboarding = completedClipboardWatchingOnboarding,
                    enableClipboardWatching = enableClipboardWatching,
                    synchronizePatternCollectionsOnMeteredNetwork = synchronizePatternCollectionsOnMeteredNetwork,
                    patternCollectionsSynchronizationPeriodSessionValue = SessionValue(
                        sessionId = patternCollectionsSynchronizationPeriodSessionId,
                        valueId = patternCollectionsSynchronizationPeriodValueId,
                        value = patternCollectionsSynchronizationPeriod,
                    ),
                    enableWindowShapeClipping = enableWindowShapeClipping,
                ),
            )
        } else {
            ResourceState.Loading
        }

    override suspend fun update(block: ComposeLifePreferencesTransform.() -> Unit) {
        val previousLoadedComposeLifePreferences = snapshotFlow { loadedPreferencesState }.firstSuccess().value

        Snapshot.withMutableSnapshot {
            object : ComposeLifePreferencesTransform {
                override val previousLoadedComposeLifePreferences: LoadedComposeLifePreferences
                    get() = previousLoadedComposeLifePreferences

                override fun setAlgorithmChoice(algorithm: AlgorithmType) {
                    algorithmChoice = algorithm
                }

                override fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
                    this@TestComposeLifePreferences.currentShapeType = currentShapeType
                }

                override fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
                    this@TestComposeLifePreferences.darkThemeConfig = darkThemeConfig
                }

                override fun setRoundRectangleConfig(
                    expected: SessionValue<CurrentShape.RoundRectangle>?,
                    newValue: SessionValue<CurrentShape.RoundRectangle>,
                ) {
                    if (expected == null || expected == SessionValue(
                            sessionId = roundRectangleSessionId,
                            valueId = roundRectangleValueId,
                            value = roundRectangleConfig,
                        )
                    ) {
                        roundRectangleConfig = newValue.value
                        roundRectangleSessionId = newValue.sessionId
                        roundRectangleValueId = newValue.valueId
                    }
                }

                override fun addQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
                    updateQuickAccessSetting(true, quickAccessSetting)

                override fun removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
                    updateQuickAccessSetting(false, quickAccessSetting)

                private fun updateQuickAccessSetting(include: Boolean, quickAccessSetting: QuickAccessSetting) {
                    if (include) {
                        quickAccessSettings += quickAccessSetting
                    } else {
                        quickAccessSettings -= quickAccessSetting
                    }
                }

                override fun setDisabledAGSL(disabled: Boolean) {
                    disableAGSL = disabled
                }

                override fun setDisableOpenGL(disabled: Boolean) {
                    disableOpenGL = disabled
                }

                override fun setDoNotKeepProcess(doNotKeepProcess: Boolean) {
                    this@TestComposeLifePreferences.doNotKeepProcess = doNotKeepProcess
                }

                override fun setTouchToolConfig(toolConfig: ToolConfig) {
                    touchToolConfig = toolConfig
                }

                override fun setStylusToolConfig(toolConfig: ToolConfig) {
                    stylusToolConfig = toolConfig
                }

                override fun setMouseToolConfig(toolConfig: ToolConfig) {
                    mouseToolConfig = toolConfig
                }

                override fun setCompletedClipboardWatchingOnboarding(completed: Boolean) {
                    completedClipboardWatchingOnboarding = completed
                }

                override fun setEnableClipboardWatching(enabled: Boolean) {
                    enableClipboardWatching = enabled
                }

                override fun setSynchronizePatternCollectionsOnMeteredNetwork(enabled: Boolean) {
                    synchronizePatternCollectionsOnMeteredNetwork = enabled
                }

                override fun setPatternCollectionsSynchronizationPeriod(
                    expected: SessionValue<DateTimePeriod>?,
                    newValue: SessionValue<DateTimePeriod>,
                ) {
                    if (expected == null || expected == SessionValue(
                            sessionId = patternCollectionsSynchronizationPeriodSessionId,
                            valueId = patternCollectionsSynchronizationPeriodValueId,
                            value = patternCollectionsSynchronizationPeriod,
                        )
                    ) {
                        patternCollectionsSynchronizationPeriod = newValue.value
                        patternCollectionsSynchronizationPeriodSessionId = newValue.sessionId
                        patternCollectionsSynchronizationPeriodValueId = newValue.valueId
                    }
                }

                override fun setEnableWindowShapeClipping(enabled: Boolean) {
                    enableWindowShapeClipping = enabled
                }
            }.run(block)
        }
    }
}

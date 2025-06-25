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
import androidx.compose.runtime.snapshots.Snapshot
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import kotlinx.datetime.DateTimePeriod
import kotlin.uuid.Uuid

@Suppress("TooManyFunctions", "LongParameterList")
class TestComposeLifePreferences(
    initialPreferences: LoadedComposeLifePreferences = LoadedComposeLifePreferences.Defaults,
) : ComposeLifePreferences, LoadedComposeLifePreferencesHolder {
    var quickAccessSettings: Set<QuickAccessSetting> by mutableStateOf(initialPreferences.quickAccessSettings)

    var algorithmChoice: AlgorithmType by mutableStateOf(initialPreferences.algorithmChoice)

    var currentShapeType: CurrentShapeType by mutableStateOf(initialPreferences.currentShapeType)

    var roundRectangleConfig: CurrentShape.RoundRectangle by mutableStateOf(
        initialPreferences.roundRectangleSessionValue.value,
    )

    var roundRectangleSessionId: Uuid by mutableStateOf(initialPreferences.roundRectangleSessionValue.sessionId)

    var roundRectangleValueId: Uuid by mutableStateOf(initialPreferences.roundRectangleSessionValue.valueId)

    var darkThemeConfig: DarkThemeConfig by mutableStateOf(initialPreferences.darkThemeConfig)

    var disableAGSL: Boolean by mutableStateOf(initialPreferences.disableAGSL)

    var disableOpenGL: Boolean by mutableStateOf(initialPreferences.disableOpenGL)

    var doNotKeepProcess: Boolean by mutableStateOf(initialPreferences.doNotKeepProcess)

    var touchToolConfig: ToolConfig by mutableStateOf(initialPreferences.touchToolConfig)

    var stylusToolConfig: ToolConfig by mutableStateOf(initialPreferences.stylusToolConfig)

    var mouseToolConfig: ToolConfig by mutableStateOf(initialPreferences.mouseToolConfig)

    var completedClipboardWatchingOnboarding:
        Boolean by mutableStateOf(initialPreferences.completedClipboardWatchingOnboarding)

    var enableClipboardWatching:
        Boolean by mutableStateOf(initialPreferences.enableClipboardWatching)

    var synchronizePatternCollectionsOnMeteredNetwork:
        Boolean by mutableStateOf(initialPreferences.synchronizePatternCollectionsOnMeteredNetwork)

    var patternCollectionsSynchronizationPeriod:
        DateTimePeriod by mutableStateOf(initialPreferences.patternCollectionsSynchronizationPeriodSessionValue.value)

    var patternCollectionsSynchronizationPeriodSessionId:
        Uuid by mutableStateOf(initialPreferences.patternCollectionsSynchronizationPeriodSessionValue.sessionId)

    var patternCollectionsSynchronizationPeriodValueId:
        Uuid by mutableStateOf(initialPreferences.patternCollectionsSynchronizationPeriodSessionValue.valueId)

    var enableWindowShapeClipping: Boolean by mutableStateOf(initialPreferences.enableWindowShapeClipping)

    override val loadedPreferencesState: ResourceState.Success<LoadedComposeLifePreferences>
        get() = ResourceState.Success(preferences)

    override val preferences: LoadedComposeLifePreferences
        get() = LoadedComposeLifePreferences(
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
        )

    override suspend fun update(block: ComposeLifePreferencesTransform.() -> Unit) {
        val previousLoadedComposeLifePreferences = preferences

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

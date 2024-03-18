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
import com.alexvanyo.composelife.sessionvaluekey.SessionValue
import java.util.UUID

@Suppress("TooManyFunctions", "LongParameterList")
class TestComposeLifePreferences(
    isLoaded: Boolean = true,
    algorithmChoice: AlgorithmType = AlgorithmType.NaiveAlgorithm,
    currentShapeType: CurrentShapeType = CurrentShapeType.RoundRectangle,
    roundRectangleConfig: CurrentShape.RoundRectangle = CurrentShape.RoundRectangle(
        sizeFraction = 1.0f,
        cornerFraction = 0.0f,
    ),
    roundRectangleSessionId: UUID = UUID.randomUUID(),
    roundRectangleValueId: UUID = UUID.randomUUID(),
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
) : ComposeLifePreferences {
    var quickAccessSettings: Set<QuickAccessSetting> by mutableStateOf(quickAccessSettings)

    var algorithmChoice: AlgorithmType by mutableStateOf(algorithmChoice)

    var currentShapeType: CurrentShapeType by mutableStateOf(currentShapeType)

    var roundRectangleConfig: CurrentShape.RoundRectangle by mutableStateOf(roundRectangleConfig)

    var roundRectangleSessionId: UUID by mutableStateOf(roundRectangleSessionId)

    var roundRectangleValueId: UUID by mutableStateOf(roundRectangleValueId)

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
                    oldSessionId: UUID?,
                    newSessionId: UUID,
                    valueId: UUID,
                    update: (CurrentShape.RoundRectangle) -> CurrentShape.RoundRectangle,
                ) {
                    if (
                        oldSessionId == null ||
                        roundRectangleSessionId == oldSessionId ||
                        roundRectangleSessionId == newSessionId
                    ) {
                        roundRectangleConfig = update(roundRectangleConfig)
                        roundRectangleSessionId = newSessionId
                        roundRectangleValueId = valueId
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
            }.run(block)
        }
    }
}

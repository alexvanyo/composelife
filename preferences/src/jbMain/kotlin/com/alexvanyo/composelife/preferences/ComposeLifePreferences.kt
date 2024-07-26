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

@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.map
import com.alexvanyo.composelife.sessionvalue.SessionValue

interface ComposeLifePreferences {
    val loadedPreferencesState: ResourceState<LoadedComposeLifePreferences>

    /**
     * Runs the given block to update the preferences.
     *
     * All updates on [ComposeLifePreferencesTransform] in the [block] are run together as a single transaction.
     */
    suspend fun update(block: ComposeLifePreferencesTransform.() -> Unit)
}

val ComposeLifePreferences.quickAccessSettingsState: ResourceState<Set<QuickAccessSetting>>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::quickAccessSettings)

val ComposeLifePreferences.algorithmChoiceState: ResourceState<AlgorithmType>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::algorithmChoice)

val ComposeLifePreferences.currentShapeTypeState: ResourceState<CurrentShapeType>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::currentShapeType)

val ComposeLifePreferences.roundRectangleSessionState: ResourceState<SessionValue<CurrentShape.RoundRectangle>>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::roundRectangleSessionValue)

val ComposeLifePreferences.currentShapeState: ResourceState<CurrentShape>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::currentShape)

val ComposeLifePreferences.darkThemeConfigState: ResourceState<DarkThemeConfig>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::darkThemeConfig)

val ComposeLifePreferences.disableAGSLState: ResourceState<Boolean>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::disableAGSL)

val ComposeLifePreferences.disableOpenGLState: ResourceState<Boolean>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::disableOpenGL)

val ComposeLifePreferences.doNotKeepProcessState: ResourceState<Boolean>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::doNotKeepProcess)

val ComposeLifePreferences.touchToolConfigState: ResourceState<ToolConfig>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::touchToolConfig)

val ComposeLifePreferences.stylusToolConfigState: ResourceState<ToolConfig>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::stylusToolConfig)

val ComposeLifePreferences.mouseToolConfigState: ResourceState<ToolConfig>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::mouseToolConfig)

val ComposeLifePreferences.completedClipboardWatchingOnboardingState: ResourceState<Boolean>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::completedClipboardWatchingOnboarding)

val ComposeLifePreferences.enableClipboardWatchingState: ResourceState<Boolean>
    get() = loadedPreferencesState.map(LoadedComposeLifePreferences::enableClipboardWatching)

suspend fun ComposeLifePreferences.setAlgorithmChoice(algorithm: AlgorithmType) =
    update { setAlgorithmChoice(algorithm) }

suspend fun ComposeLifePreferences.setCurrentShapeType(currentShapeType: CurrentShapeType) =
    update { setCurrentShapeType(currentShapeType) }

suspend fun ComposeLifePreferences.setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) =
    update { setDarkThemeConfig(darkThemeConfig) }

suspend fun ComposeLifePreferences.setRoundRectangleConfig(
    expected: SessionValue<CurrentShape.RoundRectangle>?,
    newValue: SessionValue<CurrentShape.RoundRectangle>,
) = update { setRoundRectangleConfig(expected, newValue) }

suspend fun ComposeLifePreferences.addQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
    update { addQuickAccessSetting(quickAccessSetting) }

suspend fun ComposeLifePreferences.removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
    update { removeQuickAccessSetting(quickAccessSetting) }

suspend fun ComposeLifePreferences.setDisabledAGSL(disabled: Boolean) =
    update { setDisabledAGSL(disabled) }

suspend fun ComposeLifePreferences.setDisableOpenGL(disabled: Boolean) =
    update { setDisableOpenGL(disabled) }

suspend fun ComposeLifePreferences.setDoNotKeepProcess(doNotKeepProcess: Boolean) =
    update { setDoNotKeepProcess(doNotKeepProcess) }

suspend fun ComposeLifePreferences.setTouchToolConfig(toolConfig: ToolConfig) =
    update { setTouchToolConfig(toolConfig) }

suspend fun ComposeLifePreferences.setStylusToolConfig(toolConfig: ToolConfig) =
    update { setStylusToolConfig(toolConfig) }

suspend fun ComposeLifePreferences.setMouseToolConfig(toolConfig: ToolConfig) =
    update { setMouseToolConfig(toolConfig) }

suspend fun ComposeLifePreferences.setCompletedClipboardWatchingOnboarding(completed: Boolean) =
    update { setCompletedClipboardWatchingOnboarding(completed) }

suspend fun ComposeLifePreferences.setEnableClipboardWatching(enabled: Boolean) =
    update { setEnableClipboardWatching(enabled) }

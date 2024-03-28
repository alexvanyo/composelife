/*
 * Copyright 2024 The Android Open Source Project
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

import com.alexvanyo.composelife.sessionvalue.SessionValue

@Suppress("TooManyFunctions")
interface ComposeLifePreferencesTransform {
    /**
     * The previous [LoadedComposeLifePreferences] value before this transform is applied.
     *
     * This is fixed for a given transform block: It does not change as other methods are called.
     */
    val previousLoadedComposeLifePreferences: LoadedComposeLifePreferences

    fun setAlgorithmChoice(algorithm: AlgorithmType)

    fun setCurrentShapeType(currentShapeType: CurrentShapeType)

    fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig)

    fun setRoundRectangleConfig(
        expected: SessionValue<CurrentShape.RoundRectangle>?,
        newValue: SessionValue<CurrentShape.RoundRectangle>,
    )

    fun addQuickAccessSetting(quickAccessSetting: QuickAccessSetting)

    fun removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting)

    fun setDisabledAGSL(disabled: Boolean)

    fun setDisableOpenGL(disabled: Boolean)

    fun setDoNotKeepProcess(doNotKeepProcess: Boolean)

    fun setTouchToolConfig(toolConfig: ToolConfig)

    fun setStylusToolConfig(toolConfig: ToolConfig)

    fun setMouseToolConfig(toolConfig: ToolConfig)

    fun setCompletedClipboardWatchingOnboarding(completed: Boolean)

    fun setEnableClipboardWatching(enabled: Boolean)
}

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

import com.alexvanyo.composelife.sessionvalue.SessionValue
import java.util.UUID

data class LoadedComposeLifePreferences(
    val quickAccessSettings: Set<QuickAccessSetting>,
    val algorithmChoice: AlgorithmType,
    val currentShapeType: CurrentShapeType,
    val roundRectangleSessionValue: SessionValue<CurrentShape.RoundRectangle>,
    val darkThemeConfig: DarkThemeConfig,
    val disableAGSL: Boolean,
    val disableOpenGL: Boolean,
    val doNotKeepProcess: Boolean,
    val touchToolConfig: ToolConfig,
    val stylusToolConfig: ToolConfig,
    val mouseToolConfig: ToolConfig,
    val completedClipboardWatchingOnboarding: Boolean,
    val enableClipboardWatching: Boolean,
) {
    companion object {
        internal val defaultRoundRectangleSessionId = UUID.randomUUID()

        internal val defaultRoundRectangleValueId = UUID.randomUUID()

        val Defaults = LoadedComposeLifePreferences(
            quickAccessSettings = emptySet(),
            algorithmChoice = AlgorithmType.HashLifeAlgorithm,
            currentShapeType = CurrentShapeType.RoundRectangle,
            roundRectangleSessionValue = SessionValue(
                sessionId = defaultRoundRectangleSessionId,
                valueId = defaultRoundRectangleValueId,
                value = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
            ),
            darkThemeConfig = DarkThemeConfig.FollowSystem,
            disableAGSL = false,
            disableOpenGL = false,
            doNotKeepProcess = false,
            touchToolConfig = ToolConfig.Pan,
            stylusToolConfig = ToolConfig.Draw,
            mouseToolConfig = ToolConfig.Draw,
            completedClipboardWatchingOnboarding = false,
            enableClipboardWatching = false,
        )
    }
}

val LoadedComposeLifePreferences.currentShape: CurrentShape get() =
    when (currentShapeType) {
        CurrentShapeType.RoundRectangle -> roundRectangleSessionValue.value
    }

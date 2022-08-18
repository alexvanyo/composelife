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

data class LoadedComposeLifePreferences(
    val quickAccessSettings: Set<QuickAccessSetting>,
    val algorithmChoice: AlgorithmType,
    val currentShape: CurrentShape,
    val darkThemeConfig: DarkThemeConfig,
    val disableAGSL: Boolean,
    val disableOpenGL: Boolean,
) {
    companion object {
        val Defaults = LoadedComposeLifePreferences(
            quickAccessSettings = emptySet(),
            algorithmChoice = AlgorithmType.HashLifeAlgorithm,
            currentShape = CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f,
            ),
            darkThemeConfig = DarkThemeConfig.FollowSystem,
            disableAGSL = false,
            disableOpenGL = false,
        )
    }
}

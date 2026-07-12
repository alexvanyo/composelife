/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.settings

import kotlin.test.Test
import kotlin.test.assertEquals

class SettingTests {

    @Test
    fun setting_values_are_correct() {
        val expectedValues = listOf(
            Setting.AlgorithmImplementation,
            Setting.CellStatePreview,
            Setting.DarkThemeConfig,
            Setting.CellShapeConfig,
            Setting.SynchronizePatternCollectionsOnMeteredNetwork,
            Setting.PatternCollectionsSynchronizationPeriod,
            Setting.PatternCollectionSources,
            Setting.DisableAGSL,
            Setting.DisableOpenGL,
            Setting.DoNotKeepProcess,
            Setting.EnableClipboardWatching,
            Setting.ClipboardWatchingOnboardingCompleted,
            Setting.EnableWindowShapeClipping,
        )

        assertEquals(expectedValues, Setting._values)
        assertEquals(expectedValues, Setting._sealedEnum.values)

        expectedValues.forEachIndexed { index, setting ->
            assertEquals(index, Setting._sealedEnum.ordinalOf(setting))
        }
    }

    @Test
    fun setting_names_are_correct() {
        assertEquals("Setting_AlgorithmImplementation", Setting.AlgorithmImplementation._name)
        assertEquals("Setting_CellStatePreview", Setting.CellStatePreview._name)
        assertEquals("Setting_DarkThemeConfig", Setting.DarkThemeConfig._name)
        assertEquals("Setting_CellShapeConfig", Setting.CellShapeConfig._name)
        assertEquals(
            "Setting_SynchronizePatternCollectionsOnMeteredNetwork",
            Setting.SynchronizePatternCollectionsOnMeteredNetwork._name,
        )
        assertEquals(
            "Setting_PatternCollectionsSynchronizationPeriod",
            Setting.PatternCollectionsSynchronizationPeriod._name,
        )
        assertEquals("Setting_PatternCollectionSources", Setting.PatternCollectionSources._name)
        assertEquals("Setting_DisableAGSL", Setting.DisableAGSL._name)
        assertEquals("Setting_DisableOpenGL", Setting.DisableOpenGL._name)
        assertEquals("Setting_DoNotKeepProcess", Setting.DoNotKeepProcess._name)
        assertEquals("Setting_EnableClipboardWatching", Setting.EnableClipboardWatching._name)
        assertEquals(
            "Setting_ClipboardWatchingOnboardingCompleted",
            Setting.ClipboardWatchingOnboardingCompleted._name,
        )
        assertEquals("Setting_EnableWindowShapeClipping", Setting.EnableWindowShapeClipping._name)
    }
}

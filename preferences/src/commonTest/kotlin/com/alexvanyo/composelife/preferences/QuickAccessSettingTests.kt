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

package com.alexvanyo.composelife.preferences

import kotlin.test.Test
import kotlin.test.assertEquals

class QuickAccessSettingTests {

    @Test
    fun quick_access_setting_sealed_enum_values_and_value_of_are_correct() {
        val expectedValues = listOf(
            QuickAccessSetting.AlgorithmImplementation,
            QuickAccessSetting.DarkThemeConfig,
            QuickAccessSetting.CellShapeConfig,
            QuickAccessSetting.SynchronizePatternCollectionsOnMeteredNetwork,
            QuickAccessSetting.PatternCollectionsSynchronizationPeriod,
            QuickAccessSetting.DisableAGSL,
            QuickAccessSetting.DisableOpenGL,
            QuickAccessSetting.DoNotKeepProcess,
            QuickAccessSetting.EnableClipboardWatching,
            QuickAccessSetting.ClipboardWatchingOnboardingCompleted,
            QuickAccessSetting.EnableWindowShapeClipping,
        )
        assertEquals(expectedValues, QuickAccessSetting.sealedEnum.values)
        assertEquals(expectedValues, QuickAccessSetting.values)
        expectedValues.forEach { setting ->
            assertEquals(setting, QuickAccessSetting.valueOf(setting.name))
            assertEquals(setting.ordinal, QuickAccessSetting.sealedEnum.ordinalOf(setting))
        }
    }
}

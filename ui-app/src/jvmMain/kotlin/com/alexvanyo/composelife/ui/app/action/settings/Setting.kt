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

package com.alexvanyo.composelife.ui.app.action.settings

import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.SealedEnum

/**
 * The list of settings supported by the app.
 *
 * A "setting" is a block of UI in the settings screen, which may display zero, one, or more affordances
 * to the user to update some preference.
 *
 * A setting that displays zero affordances may simply be informational, with UI to be placed in relation to other
 * settings with affordances.
 *
 * The order in which settings appear is determined by the declaration order of the subclasses of [Setting] below.
 */
sealed interface Setting {
    /**
     * The [SettingsCategory] this [Setting] belongs to.
     */
    val category: SettingsCategory

    /**
     * If not-null, this setting can be favorited and viewed for quick access as
     * represented by the given [QuickAccessSetting].
     */
    val quickAccessSetting: QuickAccessSetting?

    data object AlgorithmImplementation : Setting {
        override val category = SettingsCategory.Algorithm
        override val quickAccessSetting = QuickAccessSetting.AlgorithmImplementation
    }

    data object CellStatePreview : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = null
    }

    data object DarkThemeConfig : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = QuickAccessSetting.DarkThemeConfig
    }

    data object CellShapeConfig : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = QuickAccessSetting.CellShapeConfig
    }

    data object DisableAGSL : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DisableAGSL
    }

    data object DisableOpenGL : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DisableOpenGL
    }

    data object DoNotKeepProcess : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DoNotKeepProcess
    }

    data object EnableClipboardWatching : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.EnableClipboardWatching
    }

    data object ClipboardWatchingOnboardingCompleted : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.ClipboardWatchingOnboardingCompleted
    }

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(_sealedEnum)
    }
}

expect val Setting.Companion._sealedEnum: SealedEnum<Setting>

expect val Setting.Companion._values: List<Setting>

expect val Setting._name: String

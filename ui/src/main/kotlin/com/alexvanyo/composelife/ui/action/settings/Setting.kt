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

package com.alexvanyo.composelife.ui.action.settings

import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

sealed interface Setting {
    val category: SettingsCategory
    val quickAccessSetting: QuickAccessSetting?

    object AlgorithmImplementation : Setting {
        override val category = SettingsCategory.Algorithm
        override val quickAccessSetting = QuickAccessSetting.AlgorithmImplementation
    }

    object CellStatePreview : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = null
    }

    object DarkThemeConfig : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = QuickAccessSetting.DarkThemeConfig
    }

    object CellShapeConfig : Setting {
        override val category = SettingsCategory.Visual
        override val quickAccessSetting = QuickAccessSetting.CellShapeConfig
    }

    object DisableAGSL : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DisableAGSL
    }

    object DisableOpenGL : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DisableOpenGL
    }

    object DoNotKeepProcess : Setting {
        override val category = SettingsCategory.FeatureFlags
        override val quickAccessSetting = QuickAccessSetting.DoNotKeepProcess
    }

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

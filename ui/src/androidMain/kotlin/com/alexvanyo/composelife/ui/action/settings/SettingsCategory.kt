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

import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

/**
 * The category for a particular setting.
 */
sealed interface SettingsCategory {
    /**
     * A setting impacting the algorithm.
     */
    object Algorithm : SettingsCategory

    /**
     * A setting related to the visual display.
     */
    object Visual : SettingsCategory

    /**
     * A setting for some app feature flag.
     */
    object FeatureFlags : SettingsCategory

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

/**
 * A [Map] from the [SettingsCategory] to a list of [Setting]s in that category.
 */
private val settingsByCategory by lazy { Setting.values.groupBy(Setting::category) }

/**
 * Returns the list of [Setting]s for the given [SettingsCategory].
 */
val SettingsCategory.settings get() = settingsByCategory.getOrDefault(this, emptyList())

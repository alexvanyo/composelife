/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app

import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSurrogate
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.settings.SettingsCategory
import kotlinx.serialization.Serializable
import kotlin.uuid.Uuid

@Stable
sealed interface ComposeLifeNavigation {
    /**
     * The type of the destination.
     */
    val surrogate: ComposeLifeNavigationSurrogate

    data object CellUniverse : ComposeLifeNavigation {

        override val surrogate = Surrogate

        @Serializable
        data object Surrogate : ComposeLifeNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): ComposeLifeNavigation = CellUniverse
        }
    }

    class FullscreenSettingsList(
        initialSettingsCategory: SettingsCategory,
    ) : ComposeLifeNavigation {
        /**
         * The currently selected settings category.
         */
        var settingsCategory: SettingsCategory by mutableStateOf(initialSettingsCategory)

        val transientDetailId by derivedStateOf {
            settingsCategory
            Uuid.random()
        }

        val transientFullscreenSettingsDetail by derivedStateOf {
            transientDetailId
            FullscreenSettingsDetail(settingsCategory, null)
        }

        override val surrogate get() = Surrogate(settingsCategory)

        @Serializable
        data class Surrogate(
            val settingsCategory: SettingsCategory,
        ) : ComposeLifeNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): ComposeLifeNavigation =
                FullscreenSettingsList(settingsCategory)
        }
    }

    class FullscreenSettingsDetail(
        val settingsCategory: SettingsCategory,
        initialSettingToScrollTo: Setting?,
    ) : ComposeLifeNavigation {

        /**
         * If non-null, a [Setting] to scroll to immediately.
         */
        var settingToScrollTo: Setting? by mutableStateOf(initialSettingToScrollTo)
            private set

        /**
         * A callback that [settingToScrollTo] has been scrolled to, and shouldn't be scrolled to again.
         */
        fun onFinishedScrollingToSetting() {
            settingToScrollTo = null
        }

        override val surrogate get() = Surrogate(settingsCategory, settingToScrollTo)

        @Serializable
        data class Surrogate(
            val settingsCategory: SettingsCategory,
            val settingToScrollTo: Setting?,
        ) : ComposeLifeNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): ComposeLifeNavigation =
                FullscreenSettingsDetail(settingsCategory, settingToScrollTo)
        }
    }

    class DeserializationInfo(
        val deserializationResult: DeserializationResult,
    ) : ComposeLifeNavigation {
        override val surrogate = Surrogate(deserializationResult)

        @Serializable
        data class Surrogate(
            val deserializationResult: DeserializationResult,
        ) : ComposeLifeNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): ComposeLifeNavigation =
                DeserializationInfo(deserializationResult)
        }
    }
}

/**
 * The type for each [ComposeLifeNavigation].
 *
 * These classes must be objects, since they need to statically be able to save and restore concrete
 * [ComposeLifeNavigation] types.
 */
@Serializable
sealed interface ComposeLifeNavigationSurrogate : BackstackValueSurrogate<ComposeLifeNavigation>

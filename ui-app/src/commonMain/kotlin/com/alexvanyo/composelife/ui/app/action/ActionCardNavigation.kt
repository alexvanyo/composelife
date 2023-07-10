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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

@Stable
sealed interface ActionCardNavigation {
    /**
     * The type of the destination.
     */
    val type: ActionCardNavigationType

    /**
     * True if this destination represents a fullscreen destination.
     */
    val isFullscreen: Boolean

    object Inline : ActionCardNavigation {

        override val type = Companion
        override val isFullscreen: Boolean = false

        object Companion : ActionCardNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<ActionCardNavigation>?,
            ): Saver<Inline, Any> = Saver(
                save = { 0 },
                restore = { Inline },
            )
        }
    }

    class FullscreenSettings(
        initialSettingsCategory: SettingsCategory,
        initialShowDetails: Boolean,
        initialSettingToScrollTo: Setting?,
    ) : ActionCardNavigation {
        /**
         * The currently selected settings category.
         */
        var settingsCategory: SettingsCategory by mutableStateOf(initialSettingsCategory)

        /**
         * `true` if the details should be shown.
         */
        var showDetails: Boolean by mutableStateOf(initialShowDetails)

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

        override val type = Companion
        override val isFullscreen: Boolean = true

        companion object : ActionCardNavigationType {
            @Suppress("UnsafeCallOnNullableType")
            override fun saverFactory(
                previous: BackstackEntry<ActionCardNavigation>?,
            ): Saver<FullscreenSettings, Any> =
                listSaver(
                    save = { fullscreen ->
                        listOf(
                            with(SettingsCategory.Saver) { save(fullscreen.settingsCategory) },
                            fullscreen.showDetails,
                            fullscreen.settingToScrollTo?.let { with(Setting.Saver) { save(it) } },
                        )
                    },
                    restore = {
                        FullscreenSettings(
                            initialSettingsCategory = SettingsCategory.Saver.restore(it[0] as Int)!!,
                            initialShowDetails = it[1] as Boolean,
                            initialSettingToScrollTo = (it[2] as Int?)?.let(Setting.Saver::restore),
                        )
                    },
                )
        }
    }

    companion object {
        @Suppress("UnsafeCallOnNullableType")
        val SaverFactory: BackstackValueSaverFactory<ActionCardNavigation> = BackstackValueSaverFactory { previous ->
            listSaver(
                save = { actionCardNavigation ->
                    listOf(
                        with(ActionCardNavigationType.Saver) { save(actionCardNavigation.type) },
                        when (actionCardNavigation) {
                            is Inline ->
                                with(actionCardNavigation.type.saverFactory(previous)) {
                                    save(actionCardNavigation)
                                }

                            is FullscreenSettings ->
                                with(actionCardNavigation.type.saverFactory(previous)) {
                                    save(actionCardNavigation)
                                }
                        },
                    )
                },
                restore = { list ->
                    val type = ActionCardNavigationType.Saver.restore(list[0] as Int)!!
                    type.saverFactory(previous).restore(list[1]!!)
                },
            )
        }
    }
}

/**
 * The type for each [ActionCardNavigation].
 *
 * These classes must be objects, since they need to statically be able to save and restore concrete
 * [ActionCardNavigation] types.
 */
sealed interface ActionCardNavigationType {
    fun saverFactory(previous: BackstackEntry<ActionCardNavigation>?): Saver<out ActionCardNavigation, Any>

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

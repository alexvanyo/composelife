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

/**
 * A sealed enum of the three different backstack types for the action card.
 */
sealed interface ActionCardBackstack {
    object Speed : ActionCardBackstack
    object Edit : ActionCardBackstack
    object Settings : ActionCardBackstack

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

/**
 * The entry value for the action card navigation.
 *
 * Each entry value is a [Stable] state holder, which contains a small amount of information related to a particular
 * destination in the backstack. An entry value can be immutable, but does not have to be.
 *
 * Each entry value has an associated [type]. The associated [type] has a [ActionCardNavigationType.saverFactory] to
 * allow restoring a particular instance of [ActionCardNavigation].
 */
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

    sealed interface Speed : ActionCardNavigation {
        override val type: ActionCardNavigationType.Speed

        object Inline : Speed {
            override val type = Companion
            override val isFullscreen: Boolean = false

            object Companion : ActionCardNavigationType.Speed {
                override fun saverFactory(
                    previous: BackstackEntry<ActionCardNavigation>?,
                ): Saver<Inline, Any> = Saver(
                    save = { 0 },
                    restore = { Inline },
                )
            }
        }
    }
    sealed interface Edit : ActionCardNavigation {
        override val type: ActionCardNavigationType.Edit

        object Inline : Edit {
            override val type = Companion
            override val isFullscreen: Boolean = false

            object Companion : ActionCardNavigationType.Edit {
                override fun saverFactory(
                    previous: BackstackEntry<ActionCardNavigation>?,
                ): Saver<Inline, Any> = Saver(
                    save = { 0 },
                    restore = { Inline },
                )
            }
        }
    }
    sealed interface Settings : ActionCardNavigation {
        override val type: ActionCardNavigationType.Settings

        object Inline : Settings {
            override val type = Companion
            override val isFullscreen: Boolean = false

            object Companion : ActionCardNavigationType.Settings {
                override fun saverFactory(
                    previous: BackstackEntry<ActionCardNavigation>?,
                ): Saver<Inline, Any> = Saver(
                    save = { 0 },
                    restore = { Inline },
                )
            }
        }

        class Fullscreen(
            initialSettingsCategory: SettingsCategory,
            initialShowDetails: Boolean,
            initialSettingToScrollTo: Setting?,
        ) : Settings {
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

            companion object : ActionCardNavigationType.Settings {
                @Suppress("UnsafeCallOnNullableType")
                override fun saverFactory(
                    previous: BackstackEntry<ActionCardNavigation>?,
                ): Saver<Fullscreen, Any> =
                    listSaver(
                        save = { fullscreen ->
                            listOf(
                                with(SettingsCategory.Saver) { save(fullscreen.settingsCategory) },
                                fullscreen.showDetails,
                                fullscreen.settingToScrollTo?.let { with(Setting.Saver) { save(it) } },
                            )
                        },
                        restore = {
                            Fullscreen(
                                initialSettingsCategory = SettingsCategory.Saver.restore(it[0] as Int)!!,
                                initialShowDetails = it[1] as Boolean,
                                initialSettingToScrollTo = (it[2] as Int?)?.let(Setting.Saver::restore),
                            )
                        },
                    )
            }
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
                            is Settings.Inline ->
                                with(actionCardNavigation.type.saverFactory(previous)) {
                                    save(actionCardNavigation)
                                }

                            is Settings.Fullscreen ->
                                with(actionCardNavigation.type.saverFactory(previous)) {
                                    save(actionCardNavigation)
                                }

                            is Edit.Inline ->
                                with(actionCardNavigation.type.saverFactory(previous)) {
                                    save(actionCardNavigation)
                                }

                            is Speed.Inline ->
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

    sealed interface Speed : ActionCardNavigationType {
        override fun saverFactory(
            previous: BackstackEntry<ActionCardNavigation>?,
        ): Saver<out ActionCardNavigation.Speed, Any>

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    sealed interface Edit : ActionCardNavigationType {
        override fun saverFactory(
            previous: BackstackEntry<ActionCardNavigation>?,
        ): Saver<out ActionCardNavigation.Edit, Any>

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    sealed interface Settings : ActionCardNavigationType {
        override fun saverFactory(
            previous: BackstackEntry<ActionCardNavigation>?,
        ): Saver<out ActionCardNavigation.Settings, Any>

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

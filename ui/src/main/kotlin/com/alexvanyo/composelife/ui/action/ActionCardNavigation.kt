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

package com.alexvanyo.composelife.ui.action

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.ui.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

sealed interface ActionCardBackstack {
    object Speed : ActionCardBackstack
    object Edit : ActionCardBackstack
    object Palette : ActionCardBackstack
    object Settings : ActionCardBackstack

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

sealed interface ActionCardNavigation {
    val type: ActionCardNavigationType

    val isFullscreen: Boolean

    sealed interface Speed : ActionCardNavigation {
        override val type: ActionCardNavigationType.Speed

        object Inline : Speed {
            override val type = ActionCardNavigationType.Speed.Inline
            override val isFullscreen: Boolean = false
        }

        companion object {
            @Suppress("UnsafeCallOnNullableType")
            val Saver: Saver<Speed, Any> = listSaver(
                save = { actionCardNavigation ->
                    listOf(
                        with(ActionCardNavigationType.Speed.Saver) { save(actionCardNavigation.type) },
                        when (actionCardNavigation) {
                            is Inline -> with(ActionCardNavigationType.Speed.Inline.saver) {
                                save(actionCardNavigation)
                            }
                        },
                    )
                },
                restore = { list ->
                    val type = ActionCardNavigationType.Speed.Saver.restore(list[0] as Int)!!
                    type.saver.restore(list[1]!!)
                },
            )
        }
    }
    sealed interface Edit : ActionCardNavigation {
        override val type: ActionCardNavigationType.Edit

        object Inline : Edit {
            override val type = ActionCardNavigationType.Edit.Inline
            override val isFullscreen: Boolean = false
        }

        companion object {
            @Suppress("UnsafeCallOnNullableType")
            val Saver: Saver<Edit, Any> = listSaver(
                save = { actionCardNavigation ->
                    listOf(
                        with(ActionCardNavigationType.Edit.Saver) { save(actionCardNavigation.type) },
                        when (actionCardNavigation) {
                            is Inline -> with(ActionCardNavigationType.Edit.Inline.saver) {
                                save(actionCardNavigation)
                            }
                        },
                    )
                },
                restore = { list ->
                    val type = ActionCardNavigationType.Edit.Saver.restore(list[0] as Int)!!
                    type.saver.restore(list[1]!!)
                },
            )
        }
    }
    sealed interface Palette : ActionCardNavigation {
        override val type: ActionCardNavigationType.Palette

        object Inline : Palette {
            override val type = ActionCardNavigationType.Palette.Inline
            override val isFullscreen: Boolean = false
        }

        companion object {
            @Suppress("UnsafeCallOnNullableType")
            val Saver: Saver<Palette, Any> = listSaver(
                save = { actionCardNavigation ->
                    listOf(
                        with(ActionCardNavigationType.Palette.Saver) { save(actionCardNavigation.type) },
                        when (actionCardNavigation) {
                            is Inline -> with(ActionCardNavigationType.Palette.Inline.saver) {
                                save(actionCardNavigation)
                            }
                        },
                    )
                },
                restore = { list ->
                    val type = ActionCardNavigationType.Palette.Saver.restore(list[0] as Int)!!
                    type.saver.restore(list[1]!!)
                },
            )
        }
    }
    sealed interface Settings : ActionCardNavigation {
        override val type: ActionCardNavigationType.Settings

        object Inline : Settings {
            override val type = ActionCardNavigationType.Settings.Inline
            override val isFullscreen: Boolean = false
        }

        class Fullscreen(
            initialSettingsCategory: SettingsCategory,
            initialShowDetails: Boolean,
        ) : Settings {
            var settingsCategory by mutableStateOf(initialSettingsCategory)

            var showDetails by mutableStateOf(initialShowDetails)

            override val type = ActionCardNavigationType.Settings.Fullscreen
            override val isFullscreen: Boolean = true
        }

        companion object {
            @Suppress("UnsafeCallOnNullableType")
            val Saver: Saver<Settings, Any> = listSaver(
                save = { actionCardNavigation ->
                    listOf(
                        with(ActionCardNavigationType.Settings.Saver) { save(actionCardNavigation.type) },
                        when (actionCardNavigation) {
                            is Inline -> with(ActionCardNavigationType.Settings.Inline.saver) {
                                save(actionCardNavigation)
                            }
                            is Fullscreen -> with(ActionCardNavigationType.Settings.Fullscreen.saver) {
                                save(actionCardNavigation)
                            }
                        },
                    )
                },
                restore = { list ->
                    val type = ActionCardNavigationType.Settings.Saver.restore(list[0] as Int)!!
                    type.saver.restore(list[1]!!)
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
    val saver: Saver<out ActionCardNavigation, Any>

    sealed interface Speed : ActionCardNavigationType {
        override val saver: Saver<out ActionCardNavigation.Speed, Any>

        object Inline : Speed {
            override val saver: Saver<ActionCardNavigation.Speed.Inline, Any> = Saver(
                save = { 0 },
                restore = { ActionCardNavigation.Speed.Inline },
            )
        }

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    sealed interface Edit : ActionCardNavigationType {
        override val saver: Saver<out ActionCardNavigation.Edit, Any>

        object Inline : Edit {
            override val saver: Saver<ActionCardNavigation.Edit.Inline, Any> = Saver(
                save = { 0 },
                restore = { ActionCardNavigation.Edit.Inline },
            )
        }

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    sealed interface Palette : ActionCardNavigationType {
        override val saver: Saver<out ActionCardNavigation.Palette, Any>

        object Inline : Palette {
            override val saver: Saver<ActionCardNavigation.Palette.Inline, Any> = Saver(
                save = { 0 },
                restore = { ActionCardNavigation.Palette.Inline },
            )
        }

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    sealed interface Settings : ActionCardNavigationType {
        override val saver: Saver<out ActionCardNavigation.Settings, Any>

        object Inline : Settings {
            override val saver: Saver<ActionCardNavigation.Settings.Inline, Any> = Saver(
                save = { 0 },
                restore = { ActionCardNavigation.Settings.Inline },
            )
        }

        object Fullscreen : Settings {
            @Suppress("UnsafeCallOnNullableType")
            override val saver: Saver<ActionCardNavigation.Settings.Fullscreen, Any> =
                listSaver(
                    save = { fullscreen ->
                        listOf(
                            with(SettingsCategory.Saver) { save(fullscreen.settingsCategory) },
                            fullscreen.showDetails,
                        )
                    },
                    restore = {
                        ActionCardNavigation.Settings.Fullscreen(
                            initialSettingsCategory = SettingsCategory.Saver.restore(it[0] as Int)!!,
                            initialShowDetails = it[1] as Boolean,
                        )
                    },
                )
        }

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }

    @GenSealedEnum
    companion object
}

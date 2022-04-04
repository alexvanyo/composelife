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

import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

sealed interface ActionCardBackstack {
    object Speed : ActionCardBackstack
    object Edit : ActionCardBackstack
    object Palette : ActionCardBackstack
    object Settings : ActionCardBackstack

    @GenSealedEnum
    companion object {
        val Saver: Saver<ActionCardBackstack, Int> = sealedEnumSaver(sealedEnum)
    }
}

sealed interface ActionCardNavigation {
    val type: ActionCardNavigationType

    sealed interface Speed : ActionCardNavigation {
        override val type: ActionCardNavigationType.Speed

        object Inline : Speed {
            override val type = ActionCardNavigationType.Speed.Inline
        }

        @GenSealedEnum
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
        }

        @GenSealedEnum
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
        }

        @GenSealedEnum
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
        }

        @GenSealedEnum
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

    @GenSealedEnum
    companion object
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
            val Saver: Saver<Speed, Int> = sealedEnumSaver(sealedEnum)
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
            val Saver: Saver<Edit, Int> = sealedEnumSaver(sealedEnum)
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
            val Saver: Saver<Palette, Int> = sealedEnumSaver(sealedEnum)
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

        @GenSealedEnum
        companion object {
            val Saver: Saver<Settings, Int> = sealedEnumSaver(sealedEnum)
        }
    }

    @GenSealedEnum
    companion object
}

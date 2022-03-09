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
import androidx.compose.runtime.saveable.SaverScope
import androidx.compose.runtime.saveable.listSaver
import com.livefront.sealedenum.GenSealedEnum

sealed interface ActionCardNavigation {
    val type: ActionCardNavigationType

    object Speed : ActionCardNavigation {
        override val type = ActionCardNavigationType.Speed
    }

    object Edit : ActionCardNavigation {
        override val type = ActionCardNavigationType.Edit
    }

    object Palette : ActionCardNavigation {
        override val type = ActionCardNavigationType.Palette
    }

    object Settings : ActionCardNavigation {
        override val type = ActionCardNavigationType.Settings
    }

    companion object {
        val Saver: Saver<ActionCardNavigation, Any> = listSaver(
            save = { actionCardNavigation ->
                listOf(
                    with(ActionCardNavigationType.Saver) { save(actionCardNavigation.type) },
                    when (actionCardNavigation) {
                        is Speed -> with(ActionCardNavigationType.Speed.saver) { save(actionCardNavigation) }
                        is Edit -> with(ActionCardNavigationType.Edit.saver) { save(actionCardNavigation) }
                        is Palette -> with(ActionCardNavigationType.Palette.saver) { save(actionCardNavigation) }
                        is Settings -> with(ActionCardNavigationType.Settings.saver) { save(actionCardNavigation) }
                    }
                )
            },
            restore = { list ->
                val type = ActionCardNavigationType.Saver.restore(list[0] as Int)!!
                type.saver.restore(list[1]!!)
            }
        )
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

    object Speed : ActionCardNavigationType {
        override val saver: Saver<ActionCardNavigation.Speed, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Speed }
        )
    }

    object Edit : ActionCardNavigationType {
        override val saver: Saver<ActionCardNavigation.Edit, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Edit }
        )
    }

    object Palette : ActionCardNavigationType {
        override val saver: Saver<ActionCardNavigation.Palette, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Palette }
        )
    }

    object Settings : ActionCardNavigationType {
        override val saver: Saver<ActionCardNavigation.Settings, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Settings }
        )
    }

    @GenSealedEnum
    companion object {
        val Saver: Saver<ActionCardNavigationType, Int> = object : Saver<ActionCardNavigationType, Int> {
            override fun restore(value: Int): ActionCardNavigationType =
                ActionCardNavigationTypeSealedEnum.values[value]

            override fun SaverScope.save(value: ActionCardNavigationType): Int =
                value.ordinal
        }
    }
}

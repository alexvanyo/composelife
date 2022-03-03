package com.alexvanyo.composelife.ui

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
                        is Speed -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
                        is Edit -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
                        is Palette -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
                        is Settings -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
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

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
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

/**
 * A sealed enum of the three different inline backstack types for the inline action card navigation.
 */
sealed interface InlineActionCardBackstack {
    object Speed : InlineActionCardBackstack
    object Edit : InlineActionCardBackstack
    object Settings : InlineActionCardBackstack

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
 * Each entry value has an associated [type]. The associated [type] has a [InlineActionCardNavigationType.saverFactory]
 * to allow restoring a particular instance of [InlineActionCardNavigation].
 */
@Stable
sealed interface InlineActionCardNavigation {
    /**
     * The type of the destination.
     */
    val type: InlineActionCardNavigationType

    object Speed : InlineActionCardNavigation {
        override val type = Companion

        object Companion : InlineActionCardNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<InlineActionCardNavigation>?,
            ): Saver<Speed, Any> = Saver(
                save = { 0 },
                restore = { Speed },
            )
        }
    }

    object Edit : InlineActionCardNavigation {
        override val type = Companion

        object Companion : InlineActionCardNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<InlineActionCardNavigation>?,
            ): Saver<Edit, Any> = Saver(
                save = { 0 },
                restore = { Edit },
            )
        }
    }

    object Settings : InlineActionCardNavigation {
        override val type = Companion

        object Companion : InlineActionCardNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<InlineActionCardNavigation>?,
            ): Saver<Settings, Any> = Saver(
                save = { 0 },
                restore = { Settings },
            )
        }
    }

    companion object {
        @Suppress("UnsafeCallOnNullableType")
        val SaverFactory: BackstackValueSaverFactory<InlineActionCardNavigation> =
            BackstackValueSaverFactory { previous ->
                listSaver(
                    save = { inlineActionCardNavigation ->
                        listOf(
                            with(InlineActionCardNavigationType.Saver) { save(inlineActionCardNavigation.type) },
                            when (inlineActionCardNavigation) {
                                is Settings ->
                                    with(inlineActionCardNavigation.type.saverFactory(previous)) {
                                        save(inlineActionCardNavigation)
                                    }

                                is Edit ->
                                    with(inlineActionCardNavigation.type.saverFactory(previous)) {
                                        save(inlineActionCardNavigation)
                                    }

                                is Speed ->
                                    with(inlineActionCardNavigation.type.saverFactory(previous)) {
                                        save(inlineActionCardNavigation)
                                    }
                            },
                        )
                    },
                    restore = { list ->
                        val type = InlineActionCardNavigationType.Saver.restore(list[0] as Int)!!
                        type.saverFactory(previous).restore(list[1]!!)
                    },
                )
            }
    }
}

/**
 * The type for each [InlineActionCardNavigation].
 *
 * These classes must be objects, since they need to statically be able to save and restore concrete
 * [InlineActionCardNavigation] types.
 */
sealed interface InlineActionCardNavigationType {
    fun saverFactory(previous: BackstackEntry<InlineActionCardNavigation>?): Saver<out InlineActionCardNavigation, Any>

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

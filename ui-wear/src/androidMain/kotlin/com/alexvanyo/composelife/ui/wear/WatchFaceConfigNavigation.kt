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

package com.alexvanyo.composelife.ui.wear

import androidx.compose.runtime.Stable
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.wear.compose.foundation.lazy.ScalingLazyListState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum

/**
 * The entry value for the watchface config navigation.
 *
 * Each entry value is a [Stable] state holder, which contains a small amount of information related to a particular
 * destination in the backstack. An entry value can be immutable, but does not have to be.
 *
 * Each entry value has an associated [type]. The associated [type] has a [WatchFaceConfigNavigationType.saverFactory]
 * to allow restoring a particular instance of [WatchFaceConfigNavigation].
 */
@Stable
sealed interface WatchFaceConfigNavigation {
    val type: WatchFaceConfigNavigationType

    class List(
        val scalingLazyListState: ScalingLazyListState = ScalingLazyListState(
            initialCenterItemIndex = 0,
        ),
    ) : WatchFaceConfigNavigation {
        override val type = Companion

        companion object : WatchFaceConfigNavigationType {
            @Suppress("UnsafeCallOnNullableType")
            override fun saverFactory(
                previous: BackstackEntry<WatchFaceConfigNavigation>?,
            ): Saver<List, Any> = listSaver(
                save = {
                    listOf(
                        with(ScalingLazyListState.Saver) {
                            save(it.scalingLazyListState)
                        },
                    )
                },
                restore = { list ->
                    val scalingLazyListState = list[0]!!.let(ScalingLazyListState.Saver::restore)!!
                    List(
                        scalingLazyListState = scalingLazyListState,
                    )
                },
            )
        }
    }

    object ColorPicker : WatchFaceConfigNavigation {
        override val type = Companion

        object Companion : WatchFaceConfigNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<WatchFaceConfigNavigation>?,
            ): Saver<ColorPicker, Any> = Saver(
                save = { 0 },
                restore = { ColorPicker },
            )
        }
    }

    companion object {
        @Suppress("UnsafeCallOnNullableType")
        val SaverFactory: BackstackValueSaverFactory<WatchFaceConfigNavigation> =
            BackstackValueSaverFactory { previous ->
                listSaver(
                    save = { watchFaceConfigNavigation ->
                        listOf(
                            with(WatchFaceConfigNavigationType.Saver) { save(watchFaceConfigNavigation.type) },
                            when (watchFaceConfigNavigation) {
                                is List ->
                                    with(watchFaceConfigNavigation.type.saverFactory(previous)) {
                                        save(watchFaceConfigNavigation)
                                    }
                                is ColorPicker ->
                                    with(watchFaceConfigNavigation.type.saverFactory(previous)) {
                                        save(watchFaceConfigNavigation)
                                    }
                            },
                        )
                    },
                    restore = { list ->
                        val type = WatchFaceConfigNavigationType.Saver.restore(list[0] as Int)!!
                        type.saverFactory(previous).restore(list[1]!!)
                    },
                )
            }
    }
}

sealed interface WatchFaceConfigNavigationType {
    fun saverFactory(previous: BackstackEntry<WatchFaceConfigNavigation>?): Saver<out WatchFaceConfigNavigation, Any>

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

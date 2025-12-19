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
import androidx.wear.compose.foundation.lazy.ScalingLazyListState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSurrogate
import kotlinx.serialization.Serializable

/**
 * The entry value for the watchface config navigation.
 *
 * Each entry value is a [Stable] state holder, which contains a small amount of information related to a particular
 * destination in the backstack. An entry value can be immutable, but does not have to be.
 *
 * Each entry value has an associated [surrogate] representing the serialized form of the entry.
 */
@Stable
sealed interface WatchFaceConfigNavigation {
    val surrogate: WatchFaceConfigNavigationSurrogate

    class List(
        val scalingLazyListState: ScalingLazyListState = ScalingLazyListState(
            initialCenterItemIndex = 0,
        ),
    ) : WatchFaceConfigNavigation {
        override val surrogate get() = Surrogate(
            centerItemIndex = scalingLazyListState.centerItemIndex,
            centerItemScrollOffset = scalingLazyListState.centerItemScrollOffset,
        )

        @Serializable
        data class Surrogate(
            val centerItemIndex: Int,
            val centerItemScrollOffset: Int,
        ) : WatchFaceConfigNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<WatchFaceConfigNavigation>?,
            ): WatchFaceConfigNavigation =
                List(
                    ScalingLazyListState(
                        initialCenterItemIndex = centerItemIndex,
                        initialCenterItemScrollOffset = centerItemScrollOffset,
                    ),
                )
        }
    }

    data object ColorPicker : WatchFaceConfigNavigation {
        override val surrogate = Surrogate

        @Serializable
        data object Surrogate : WatchFaceConfigNavigationSurrogate {
            override fun createFromSurrogate(
                previous: BackstackEntry<WatchFaceConfigNavigation>?,
            ): WatchFaceConfigNavigation = ColorPicker
        }
    }
}

@Serializable
sealed interface WatchFaceConfigNavigationSurrogate : BackstackValueSurrogate<WatchFaceConfigNavigation>

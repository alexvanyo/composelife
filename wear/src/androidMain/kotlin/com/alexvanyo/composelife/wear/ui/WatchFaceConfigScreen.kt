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

package com.alexvanyo.composelife.wear.ui

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.res.imageResource
import androidx.wear.compose.foundation.lazy.rememberScalingLazyListState
import androidx.wear.compose.material.PositionIndicator
import androidx.wear.compose.material.Scaffold
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.ui.util.WearDevicePreviews
import com.alexvanyo.composelife.wear.R
import com.alexvanyo.composelife.wear.theme.ComposeLifeTheme
import kotlinx.coroutines.awaitCancellation

@Composable
fun WatchFaceConfigScreen(
    state: WatchFaceConfigState,
    modifier: Modifier = Modifier,
) {
    val navigationController =
        rememberMutableBackstackNavigationController(
            initialBackstackEntries = listOf(
                BackstackEntry(
                    value = WatchFaceConfigNavigation.List,
                    previous = null,
                ),
            ),
            saver = WatchFaceConfigNavigation.Saver
        )

    val listScalingLazyColumnState = rememberScalingLazyListState(
        initialCenterItemIndex = 0,
    )

    Scaffold(
        positionIndicator = when (navigationController.currentEntry.value) {
            WatchFaceConfigNavigation.List -> {
                {
                    PositionIndicator(listScalingLazyColumnState)
                }
            }
            WatchFaceConfigNavigation.ColorPicker -> null
        },
        modifier = modifier,
    ) {
        WearNavigationHost(
            navigationController = navigationController
        ) { entry ->
            when (entry.value) {
                WatchFaceConfigNavigation.List -> {
                    WatchFaceConfigList(
                        state = state,
                        onEditColorClicked = {
                            navigationController.withExpectedActor(entry.id) {
                                navigate(WatchFaceConfigNavigation.ColorPicker)
                            }
                        },
                        scalingLazyListState = listScalingLazyColumnState
                    )
                }
                WatchFaceConfigNavigation.ColorPicker -> {
                    WatchFaceColorPicker(
                        color = state.color,
                        setColor = { state.color = it }
                    )
                }
            }
        }
    }
}

@WearDevicePreviews
@Composable
fun WatchFaceConfigScreenPreview() {
    ComposeLifeTheme {
        val preview = ImageBitmap.imageResource(id = R.drawable.watchface_square)

        WatchFaceConfigScreen(
            state = object : WatchFaceConfigState {
                override suspend fun update(): Nothing = awaitCancellation()

                override var color: Color = Color.White

                override val preview get() = preview

                override fun openComplicationDataSourceChooser(id: Int) = Unit
            }
        )
    }
}

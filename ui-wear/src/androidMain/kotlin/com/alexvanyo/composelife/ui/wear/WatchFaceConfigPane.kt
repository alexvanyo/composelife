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

import androidx.activity.compose.BackHandler
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMapSerializer
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor

@Suppress("IgnoredReturnValue")
@Composable
fun WatchFaceConfigPane(
    state: WatchFaceConfigState,
    modifier: Modifier = Modifier,
) {
    val navigationController =
        rememberMutableBackstackNavigationController(
            initialBackstackEntries = listOf(
                BackstackEntry(
                    value = WatchFaceConfigNavigation.List(),
                    previous = null,
                ),
            ),
            backstackMapSerializer = BackstackMapSerializer(
                convertToSurrogate = WatchFaceConfigNavigation::surrogate,
            ),
        )

    BackHandler(navigationController.canNavigateBack) {
        navigationController.popBackstack()
    }

    WearNavDisplay(
        navigationController = navigationController,
        modifier = modifier,
    ) { entry ->
        when (val value = entry.value) {
            is WatchFaceConfigNavigation.List -> {
                WatchFaceConfigList(
                    state = state,
                    onEditColorClicked = {
                        navigationController.withExpectedActor(entry.id) {
                            navigate(WatchFaceConfigNavigation.ColorPicker)
                        }
                    },
                    scalingLazyListState = value.scalingLazyListState,
                )
            }
            WatchFaceConfigNavigation.ColorPicker -> {
                WatchFaceColorPicker(
                    color = state.color,
                    setColor = { state.color = it },
                )
            }
        }
    }
}

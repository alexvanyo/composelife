/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.navigation

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier

/**
 * The simplest [NavigationDecoration] implementation, which just displays the current pane with a jumpcut.
 */
@Composable
fun <T : NavigationEntry> JumpcutNavigationDecoration(
    renderableNavigationState: RenderableNavigationState<T, NavigationState<T>>,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        renderableNavigationState.renderablePanes.getValue(
            renderableNavigationState.navigationState.currentEntryId,
        ).invoke()
    }
}

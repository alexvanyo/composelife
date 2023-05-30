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

package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier

/**
 * The primary composable for displaying a [NavigationState].
 *
 * This automatically animated transitions between content, which is rendered for the current top-most entry with the
 * id of [NavigationState.currentEntryId] as specified in [content].
 *
 * The state for each entry is independently saved via [rememberSaveableStateHolder], and the corresponding state is
 * cleared when the keys are observed to no longer be in the backstack map.
 *
 * TODO: Remove when AnimatedContent is the same in desktop and Android.
 */
@Composable
expect fun <T : NavigationEntry> NavigationHost(
    navigationState: NavigationState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    content: @Composable (T) -> Unit,
)

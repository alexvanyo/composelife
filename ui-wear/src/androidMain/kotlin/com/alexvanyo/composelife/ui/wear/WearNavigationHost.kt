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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Modifier
import androidx.wear.compose.foundation.ExperimentalWearFoundationApi
import androidx.wear.compose.foundation.HierarchicalFocusCoordinator
import androidx.wear.compose.material.SwipeToDismissBox
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.FinalizingNavigationDecoration
import com.alexvanyo.composelife.navigation.MutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.popBackstack
import java.util.UUID

@Composable
fun <T> WearNavigationHost(
    navigationController: MutableBackstackNavigationController<T>,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) = WearNavigationHost(
    backstackState = navigationController,
    onNavigateBack = { navigationController.popBackstack() },
    modifier = modifier,
    content = content,
)

@Composable
fun <T> WearNavigationHost(
    backstackState: BackstackState<T>,
    onNavigateBack: () -> Unit,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) = NavigationHost(
    navigationState = backstackState,
    modifier = modifier,
    decoration = wearNavigationDecoration(
        onNavigateBack = onNavigateBack,
    ),
    content = content,
)

@OptIn(ExperimentalWearFoundationApi::class)
fun <T> wearNavigationDecoration(
    onNavigateBack: () -> Unit,
): FinalizingNavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { renderableNavigationState ->
    val movablePanes = renderableNavigationState.renderablePanes.mapValues { (id, paneContent) ->
        key(id) {
            val currentPaneContent by rememberUpdatedState(paneContent)
            remember {
                movableContentOf {
                    currentPaneContent()
                }
            }
        }
    }
    val currentEntry = renderableNavigationState.navigationState.currentEntry

    SwipeToDismissBox(
        onDismissed = onNavigateBack,
        backgroundKey = currentEntry.previous?.id ?: remember { UUID.randomUUID() },
        contentKey = currentEntry.id,
        hasBackground = currentEntry.previous != null,
    ) { isBackground ->
        val entry = if (isBackground) {
            checkNotNull(currentEntry.previous) {
                "Current entry had no previous, should not be showing background!"
            }
        } else {
            currentEntry
        }

        HierarchicalFocusCoordinator(
            requiresFocus = { currentEntry.id == entry.id },
        ) {
            key(entry.id) {
                // Fetch and store the movable content to hold onto while animating out
                val movablePane = remember { movablePanes.getValue(entry.id) }
                movablePane()
            }
        }
    }
}

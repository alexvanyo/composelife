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
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Modifier
import androidx.wear.compose.material.SwipeToDismissBox
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.MutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
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
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.map(UUID::toString) },
            restore = {
                mutableStateSetOf<UUID>().apply {
                    addAll(it.map(UUID::fromString))
                }
            },
        ),
    ) { mutableStateSetOf<UUID>() }

    SwipeToDismissBox(
        onDismissed = onNavigateBack,
        backgroundKey = backstackState.currentEntry.previous?.id ?: remember { UUID.randomUUID() },
        contentKey = backstackState.currentEntry.id,
        hasBackground = backstackState.currentEntry.previous != null,
        modifier = modifier,
    ) { isBackground ->
        val entry = if (isBackground) {
            checkNotNull(backstackState.currentEntry.previous) {
                "Current entry had no previous, should not be showing background!"
            }
        } else {
            backstackState.currentEntry
        }

        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet: Set<UUID> = backstackState.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
        (allKeys - keySet).forEach(stateHolder::removeState)
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.addAll(keySet)
    }
}

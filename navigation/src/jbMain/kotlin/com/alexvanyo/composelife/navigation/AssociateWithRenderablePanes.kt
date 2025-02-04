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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import com.slack.circuit.retained.LocalCanRetainChecker
import com.slack.circuit.retained.rememberRetainedStateHolder

/**
 * Returns a [RenderableNavigationState] associating the entries for the [navigationState] with a lambda to
 * display that content.
 *
 * This transforms [pane], a general lambda to render a [NavigationEntry] of type [T], into instance specific
 * lambdas for each navigation entry.
 */
@Composable
fun <T : NavigationEntry, S : NavigationState<T>> associateWithRenderablePanes(
    navigationState: S,
    pane: @Composable (T) -> Unit,
): RenderableNavigationState<T, S> {
    val saveableStateHolder = rememberSaveableStateHolder()
    val retainedStateHolder = rememberRetainedStateHolder()

    val currentEntryKeySet by rememberUpdatedState(navigationState.entryMap.keys.toSet())

    // Set up a DisposableEffect for each entry key in the backstack to clear a particular entry's state from the
    // retainedStateRegistry when the entry is no longer in the backstack.
    // Without this, entry state would leak and be kept around indefinitely in the case where an entry is removed
    // from the backstack while not currently being rendered.
    currentEntryKeySet.forEach { entryKey ->
        key(entryKey) {
            DisposableEffect(Unit) {
                // Ordering notes
                // This will happen _after_ the RetainedStateProvider's onDispose in
                // due to LIFO ordering of DisposableEffect, so any retained entry state that was saved will be cleared.
                // If the entry is still visible, then the can retain checker below will avoiding retaining the state
                // if saved by a parent.
                // This will happen _after_ the content's onDispose in SaveableStateProvider due to
                // LIFO ordering of DisposableEffect, so any saved state will be cleared. If the entry is still visible,
                // then removing this state will prevent the entry state from being saved when it disappears.
                onDispose {
                    if (entryKey !in currentEntryKeySet) {
                        retainedStateHolder.removeState(entryKey.toString())
                        saveableStateHolder.removeState(entryKey)
                    }
                }
            }
        }
    }

    val wrappedPane: @Composable (T) -> Unit = { entry ->
        saveableStateHolder.SaveableStateProvider(key = entry.id) {
            CompositionLocalProvider(
                // Only retain the entry when it is in the backstack.
                // Remember the CanRetainChecker lambda to avoid propagating changes through the tree
                LocalCanRetainChecker provides remember(entry.id) {
                    { _ -> entry.id in currentEntryKeySet }
                },
            ) {
                retainedStateHolder.RetainedStateProvider(key = entry.id.toString()) {
                    pane(entry)
                }
            }
        }
    }

    val currentWrappedPane by rememberUpdatedState(wrappedPane)

    return RenderableNavigationState(
        navigationState,
        navigationState.entryMap.mapValues { (id, entry) ->
            key(id) {
                val currentEntry by rememberUpdatedState(entry)
                remember {
                    @Composable { currentWrappedPane.invoke(currentEntry) }
                }
            }
        },
    )
}

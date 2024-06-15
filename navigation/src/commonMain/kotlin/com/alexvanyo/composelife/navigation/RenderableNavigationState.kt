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
import com.slack.circuit.retained.CanRetainChecker
import com.slack.circuit.retained.LocalCanRetainChecker
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.RetainedStateRegistry
import com.slack.circuit.retained.rememberRetained
import java.util.UUID

class RenderableNavigationState<T : NavigationEntry, S : NavigationState<T>>(
    val navigationState: S,
    val renderablePanes: Map<UUID, @Composable () -> Unit>,
)

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

    /**
     * Create a [RetainedStateRegistry] for the NavigationHost.
     * This will keep all individual entry's [RetainedStateRegistry]s retained even if they are not composed.
     */
    val retainedStateRegistry = rememberRetained { RetainedStateRegistry() }

    val currentEntryKeySet by rememberUpdatedState(navigationState.entryMap.keys.toSet())

    // Set up a DisposableEffect for each entry key in the backstack to clear a particular entry's state from the
    // retainedStateRegistry when the entry is no longer in the backstack.
    // Without this, entry state would leak and be kept around indefinitely in the case where an entry is removed
    // from the backstack while not currently being rendered.
    currentEntryKeySet.forEach { entryKey ->
        key(entryKey) {
            DisposableEffect(Unit) {
                // Ordering notes
                // This will happen _after_ the entryRetainedStateRegistry's onDispose in
                // due to LIFO ordering of DisposableEffect, so any retained entry state saved there will be cleared.
                // This will happen _after_ the content's onDispose in SaveableStateProvider due to
                // LIFO ordering of DisposableEffect, so the removed entry state saving will be skipped.
                onDispose {
                    if (entryKey !in currentEntryKeySet) {
                        retainedStateRegistry.consumeValue(entryKey.toString())
                        saveableStateHolder.removeState(entryKey)
                    }
                }
            }
        }
    }

    val wrappedPane: @Composable (T) -> Unit = { entry ->
        saveableStateHolder.SaveableStateProvider(key = entry.id) {
            CompositionLocalProvider(
                LocalRetainedStateRegistry provides retainedStateRegistry,
                /**
                 * Only retain the entry [RetainedStateRegistry] when it is in the backstack.
                 */
                LocalCanRetainChecker provides { entry.id in currentEntryKeySet },
            ) {
                val entryRetainedStateRegistry = rememberRetained(key = entry.id.toString()) {
                    RetainedStateRegistry()
                }

                CompositionLocalProvider(
                    LocalRetainedStateRegistry provides entryRetainedStateRegistry,
                    LocalCanRetainChecker provides CanRetainChecker.Always,
                ) {
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

/**
 * A navigation transform from a [RenderableNavigationState] of [T1] and [S1] into a
 * [RenderableNavigationState] of [T2] and [S2].
 */
typealias RenderableNavigationTransform<T1, S1, T2, S2> =
    @Composable (RenderableNavigationState<T1, S1>) -> RenderableNavigationState<T2, S2>

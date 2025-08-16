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
import androidx.compose.runtime.ControlledRetainScope
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.ForgetfulRetainScope
import androidx.compose.runtime.LocalRetainScope
import androidx.compose.runtime.RetainStateProvider
import androidx.compose.runtime.currentComposer
import androidx.compose.runtime.currentCompositionLocalContext
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.retain
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.runtime.setValue

/**
 * Returns a [RenderableNavigationState] associating the entries for the [navigationState] with a lambda to
 * display that content.
 *
 * This transforms [pane], a general lambda to render a [NavigationEntry] of type [T], into instance specific
 * lambdas for each navigation entry.
 */
@Suppress("LongMethod")
@Composable
fun <T : NavigationEntry, S : NavigationState<T>> associateWithRenderablePanes(
    navigationState: S,
    pane: @Composable (T) -> Unit,
): RenderableNavigationState<T, S> {
    val saveableStateHolder = rememberSaveableStateHolder()

    val currentEntryKeySet by rememberUpdatedState(navigationState.entryMap.keys.toSet())

    val entryRetainScopes = currentEntryKeySet.associateWith { entryKey ->
        key(entryKey) {
            retain { ControlledRetainScope() }
        }
    }

    // Set up a DisposableEffect for each entry key in the backstack to clear a particular entry's state from the
    // saveableStateHolder when the entry is no longer in the backstack.
    // Without this, entry state would leak and be kept around indefinitely in the case where an entry is removed
    // from the backstack while not currently being rendered.
    currentEntryKeySet.forEach { entryKey ->
        key(entryKey) {
            val entryRetainScope = entryRetainScopes.getValue(entryKey)
            DisposableEffect(Unit) {
                // Ordering notes
                // This will happen _after_ the content's onDispose in SaveableStateProvider due to
                // LIFO ordering of DisposableEffect, so any saved state will be cleared. If the entry is still visible,
                // then removing this state will prevent the entry state from being saved when it disappears.
                // This will happen _after_ the content's retain onDispose s due to
                // LIFO ordering of DisposableEffect, so any retained values will be cleared. If the entry is still
                // visible, then it won't start saving in the DisposableEffect below
                onDispose {
                    if (entryKey !in currentEntryKeySet) {
                        entryRetainScope.setParentRetainStateProvider(RetainStateProvider.NeverKeepExitedValues)
                        // If the entryRetainScope is still keeping exited values, this means that we started making
                        // the direct call to startKeepingExitedValues as the content is gone, but we no longer want to
                        // retain
                        if (entryRetainScope.isKeepingExitedValues) {
                            entryRetainScope.stopKeepingExitedValues()
                        }
                        saveableStateHolder.removeState(entryKey)
                    }
                }
            }
        }
    }

    val wrappedPane: @Composable (T) -> Unit = { entry ->
        saveableStateHolder.SaveableStateProvider(key = entry.id) {
            val parentScope = LocalRetainScope.current
            val entryRetainScope = remember { entryRetainScopes.getValue(entry.id) }

            CompositionLocalProvider(LocalRetainScope provides entryRetainScope) {
                pane(entry)
            }

            @Suppress("ComposeRememberMissing")
            var isRetaining by retain { mutableStateOf(false) }
            var isDisposingCompletely by remember { mutableStateOf(false) }

            DisposableEffect(parentScope) {
                entryRetainScope.setParentRetainStateProvider(parentScope)
                onDispose {
                    // If we aren't disposing completely, then that means the parent scope is
                    // changing.
                    // Keep the parent's state until we get a new scope.
                    if (!isDisposingCompletely) {
                        entryRetainScope.setParentRetainStateProvider(
                            if (parentScope.isKeepingExitedValues) {
                                RetainStateProvider.AlwaysKeepExitedValues
                            } else {
                                RetainStateProvider.NeverKeepExitedValues
                            },
                        )
                    }
                }
            }

            val composer = currentComposer
            DisposableEffect(Unit) {
                // Stop keeping exited values when we come back after retaining
                val cancellationHandle =
                    composer.scheduleFrameEndCallback {
                        if (isRetaining) {
                            entryRetainScope.stopKeepingExitedValues()
                            isRetaining = false
                        }
                    }

                onDispose {
                    cancellationHandle.cancel()
                    isDisposingCompletely = true
                    // Start keeping exited values when we leave if the entry is still in entry key set
                    if (entry.id in currentEntryKeySet) {
                        isRetaining = true
                        entryRetainScope.startKeepingExitedValues()
                    }
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

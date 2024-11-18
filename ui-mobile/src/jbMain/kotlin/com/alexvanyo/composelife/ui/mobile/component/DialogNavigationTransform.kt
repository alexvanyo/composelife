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

package com.alexvanyo.composelife.ui.mobile.component

import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionLayout
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackRenderableNavigationTransformResult
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationSegment
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.RenderableNavigationTransform
import com.alexvanyo.composelife.navigation.backstackRenderableNavigationTransform
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.util.CrossfadePredictiveNavigationFrame
import com.alexvanyo.composelife.ui.util.LocalNavigationSharedTransitionScope
import com.alexvanyo.composelife.ui.util.PlatformEdgeToEdgeDialog
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackHandler
import com.alexvanyo.composelife.ui.util.rememberRepeatablePredictiveBackStateHolder
import com.alexvanyo.composelife.ui.util.uuidSaver
import kotlin.uuid.Uuid

fun <T> dialogNavigationTransform(
    onBackButtonPressed: () -> Unit,
): RenderableNavigationTransform<
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    > =
    { renderableNavigationState ->
        val seedPaneIds = renderableNavigationState.calculateSeedPaneIds()

        val paneIdToIsDialog = renderableNavigationState.navigationState
            .entryMap
            .mapValues { (_, entry) ->
                key(entry.id) {
                    val isDialog by rememberUpdatedState(entry.value.isDialog())
                    remember { { isDialog } }
                }
            }

        val nonDialogPaneIds = renderableNavigationState.navigationState
            .entryMap
            .entries
            .mapNotNull { entry ->
                (entry.key to key(entry.key) { rememberSaveable(saver = uuidSaver) { Uuid.random() } }).takeUnless {
                    paneIdToIsDialog.getValue(entry.key).invoke()
                }
            }
            .toMap()

        backstackRenderableNavigationTransform<NavigationSegment<T>, NavigationSegment<T>> { entry, movablePanes ->
            entryTransform(
                seedPaneIds = seedPaneIds,
                paneIdToIsDialog = paneIdToIsDialog,
                nonDialogPaneIds = nonDialogPaneIds,
                onBackButtonPressed = onBackButtonPressed,
                entry = entry,
                movablePanes = movablePanes,
            )
        }.invoke(renderableNavigationState)
    }

@OptIn(ExperimentalSharedTransitionApi::class)
@Suppress("LongParameterList", "LongMethod")
@Composable
private fun <T> entryTransform(
    seedPaneIds: Set<Uuid>,
    paneIdToIsDialog: Map<Uuid, () -> Boolean>,
    nonDialogPaneIds: Map<Uuid, Uuid>,
    onBackButtonPressed: () -> Unit,
    entry: BackstackEntry<NavigationSegment<T>>,
    movablePanes: Map<Uuid, @Composable () -> Unit>,
): BackstackRenderableNavigationTransformResult<NavigationSegment<T>>? =
    if (entry.id in seedPaneIds) {
        val dialogableEntryGroup = entry.createDialogableEntryGroup()
        val nonDialogEntry = dialogableEntryGroup.last()
        val newEntryId =
            remember(nonDialogEntry.id) { nonDialogPaneIds.getValue(nonDialogEntry.id) }

        val dialogEntries = dialogableEntryGroup.dropLast(1)

        val dialogRenderableNavigationState by key(newEntryId) {
            rememberUpdatedState(
                createDialogRenderableNavigationState(
                    dialogEntries = dialogEntries,
                    movablePanes = movablePanes,
                    currentEntryId = entry.id,
                    paneIdToIsDialog = paneIdToIsDialog,
                ),
            )
        }

        val newPane = key(newEntryId) {
            @Composable {
                val pane = remember { movablePanes.getValue(nonDialogEntry.id) }
                val isDialog = remember {
                    paneIdToIsDialog.getValue(nonDialogEntry.id)
                }.invoke()
                val visible = !isDialog

                Box {
                    if (visible) {
                        pane()
                    }
                }

                if (dialogEntries.isNotEmpty()) {
                    PlatformEdgeToEdgeDialog(
                        onDismissRequest = onBackButtonPressed,
                    ) {
                        SharedTransitionLayout {
                            CompositionLocalProvider(LocalNavigationSharedTransitionScope provides null) {
                                val repeatablePredictiveBackStateHolder =
                                    rememberRepeatablePredictiveBackStateHolder()

                                RepeatablePredictiveBackHandler(
                                    repeatablePredictiveBackStateHolder = repeatablePredictiveBackStateHolder,
                                    enabled = dialogEntries.size > 1,
                                    onBack = onBackButtonPressed,
                                )

                                CrossfadePredictiveNavigationFrame(
                                    dialogRenderableNavigationState,
                                    repeatablePredictiveBackStateHolder.value,
                                )
                            }
                        }
                    }
                }
            }
        }

        val currentNewPane by key(newEntryId) { rememberUpdatedState(newPane) }

        BackstackRenderableNavigationTransformResult(
            id = newEntryId,
            value = object : NavigationSegment.CombinedSegment<T> {
                override val combinedValues =
                    dialogableEntryGroup.flatMap {
                        it.value.combinedValues
                    }
            },
            previousPreTransformedId = nonDialogEntry.previous?.id,
            pane = key(newEntryId) {
                @Composable {
                    currentNewPane.invoke()
                }
            },
        )
    } else {
        null
    }

@Composable
private fun <T> createDialogRenderableNavigationState(
    dialogEntries: List<BackstackEntry<NavigationSegment<T>>>,
    movablePanes: Map<Uuid, @Composable () -> Unit>,
    currentEntryId: Uuid,
    paneIdToIsDialog: Map<Uuid, () -> Boolean>,
): RenderableNavigationState<BackstackEntry<NavigationSegment<T>>, BackstackState<NavigationSegment<T>>> =
    RenderableNavigationState<
        BackstackEntry<NavigationSegment<T>>,
        BackstackState<NavigationSegment<T>>,
        >(
        navigationState = object : BackstackState<NavigationSegment<T>> {
            override val entryMap: BackstackMap<NavigationSegment<T>>
                get() = dialogEntries.associateBy(BackstackEntry<NavigationSegment<T>>::id)
            override val currentEntryId: Uuid
                get() = currentEntryId
        },
        renderablePanes = movablePanes.mapValues { (id, pane) ->
            key(id) {
                @Composable {
                    val isDialog = remember { paneIdToIsDialog.getValue(id) }.invoke()
                    val visible = isDialog

                    Box {
                        if (visible) {
                            pane()
                        }
                    }
                }
            }
        },
    )

private fun <T> NavigationSegment<T>.isDialog() = when (this) {
    is NavigationSegment.SingleSegment<*> -> {
        val value = this.value
        value is DialogableEntry && value.isDialog
    }
    is NavigationSegment.CombinedSegment<*> -> combinedValues.all {
        it is DialogableEntry && it.isDialog
    }
}

@Composable
private fun <T> BackstackEntry<NavigationSegment<T>>.createDialogableEntryGroup():
    List<BackstackEntry<NavigationSegment<T>>> = buildList {
    var currentEntry: BackstackEntry<NavigationSegment<T>>? = this@createDialogableEntryGroup
    while (currentEntry != null) {
        add(currentEntry)
        currentEntry = currentEntry.previous?.takeIf { currentEntry.value.isDialog() }
    }
}

@Suppress("ComposeUnstableReceiver")
@Composable
private fun <T> RenderableNavigationState<
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    >.calculateSeedPaneIds(): Set<Uuid> {
    val seedPaneIds = mutableSetOf<Uuid>()
    val nonSeedPaneIds = mutableSetOf<Uuid>()

    @Composable
    fun visitEntry(nav: BackstackEntry<NavigationSegment<T>>) {
        if (nav.id in nonSeedPaneIds) return
        if (nav.id in seedPaneIds) return

        seedPaneIds.add(nav.id)
        val dialogableEntryGroup = nav.createDialogableEntryGroup()
        nonSeedPaneIds.addAll(dialogableEntryGroup.drop(1).map(BackstackEntry<NavigationSegment<T>>::id))
    }

    // First, generate entries iterating through the current backstack hierarchy with the previous pointers
    generateSequence(
        navigationState.currentEntry,
        BackstackEntry<NavigationSegment<T>>::previous,
    ).forEach { visitEntry(it) }

    // Second, iterate through all of the entries, to generate any missing entries that are not part of the current
    // backstack hierarchy
    navigationState.entryMap.values.forEach { visitEntry(it) }

    return seedPaneIds
}

interface DialogableEntry {
    val isDialog: Boolean
}

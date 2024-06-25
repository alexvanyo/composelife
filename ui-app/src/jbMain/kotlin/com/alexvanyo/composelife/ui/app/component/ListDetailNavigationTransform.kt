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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationSegment
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.RenderableNavigationTransform
import java.util.UUID

/**
 * A [RenderableNavigationTransform] to display multiple panes in a list-detail layout, if there is enough room
 * to display both. If there isn't room to display both the list and the detail, then just one will be shown based
 * on the [ListEntry] and [DetailEntry]'s [ListDetailInfo].
 *
 * This transform will only operate on single segments with a value that implements [ListEntry] and [DetailEntry].
 *
 * This transform works with the invariant that these entries are always paired, with a [ListEntry] _always_ being the
 * previous entry to the paired [DetailEntry].
 *
 * It is invalid for a [ListEntry] to be alone, or a [DetailEntry] to be alone - it is the responsibility of the
 * code maintaining the [BackstackState] to enforce this invariant.
 */
@Suppress("LongMethod", "CyclomaticComplexMethod")
fun <T> listDetailNavigationTransform(
    onBackButtonPressed: () -> Unit,
): RenderableNavigationTransform<
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    > = { renderableNavigationState ->
    val entryMap = renderableNavigationState.navigationState.entryMap
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

    val idsTransform = renderableNavigationState.navigationState.entryMap
        .filterValues {
            val navigationSegment = it.value
            navigationSegment !is NavigationSegment.SingleSegment || navigationSegment.value !is ListEntry
        }
        .mapValues { (_, entry) ->
            when (val navigationSegment = entry.value) {
                is NavigationSegment.SingleSegment -> {
                    when (navigationSegment.value) {
                        is DetailEntry -> entry.previous!!.id
                        else -> entry.id
                    }
                }
                is NavigationSegment.CombinedSegment -> entry.id
            }
        }

    val transformedPaneMap: Map<UUID, @Composable () -> Unit> = entryMap
        .filterValues {
            val navigationSegment = it.value
            navigationSegment !is NavigationSegment.SingleSegment || navigationSegment.value !is ListEntry
        }
        .mapKeys { (_, entry) ->
            when (val navigationSegment = entry.value) {
                is NavigationSegment.SingleSegment -> {
                    when (navigationSegment.value) {
                        is DetailEntry -> entry.previous!!.id
                        else -> entry.id
                    }
                }
                is NavigationSegment.CombinedSegment -> entry.id
            }
        }
        .mapValues { (id, entry) ->
            key(id) {
                when (val navigationSegment = entry.value) {
                    is NavigationSegment.SingleSegment -> {
                        when (val value = navigationSegment.value) {
                            is DetailEntry -> {
                                {
                                    val previous = entry.previous
                                    requireNotNull(previous)
                                    @Suppress("UNCHECKED_CAST")
                                    val listEntry: ListEntry =
                                        (previous.value as NavigationSegment.SingleSegment<ListEntry>).value
                                    val detailEntry: DetailEntry = value

                                    ListDetailPaneScaffold(
                                        showList = listEntry.isListVisible,
                                        showDetail = detailEntry.isDetailVisible,
                                        listContent = {
                                            remember(previous.id) { movablePanes.getValue(previous.id) }.invoke()
                                        },
                                        detailContent = {
                                            remember(entry.id) { movablePanes.getValue(entry.id) }.invoke()
                                        },
                                        onBackButtonPressed = onBackButtonPressed,
                                    )
                                }
                            }
                            else -> {
                                {
                                    // No-op transform for other entries
                                    remember { movablePanes.getValue(entry.id) }.invoke()
                                }
                            }
                        }
                    }
                    is NavigationSegment.CombinedSegment<T> -> {
                        {
                            // No-op transform for other entries
                            remember { movablePanes.getValue(entry.id) }.invoke()
                        }
                    }
                }
            }
        }

    val transformedEntryMap = entryMap
        .filterValues {
            val navigationSegment = it.value
            navigationSegment !is NavigationSegment.SingleSegment || navigationSegment.value !is ListEntry
        }
        .mapKeys { (_, entry) ->
            when (val navigationSegment = entry.value) {
                is NavigationSegment.SingleSegment -> {
                    when (navigationSegment.value) {
                        is DetailEntry -> entry.previous!!.id
                        else -> entry.id
                    }
                }
                is NavigationSegment.CombinedSegment -> entry.id
            }
        }
        .mapValues { (_, entry) ->
            when (val navigationSegment = entry.value) {
                is NavigationSegment.SingleSegment -> {
                    when (navigationSegment.value) {
                        is DetailEntry -> BackstackEntry(
                            object : NavigationSegment.CombinedSegment<T> {
                                override val combinedValues =
                                    entry.previous!!.value.combinedValues + entry.value.combinedValues
                            },
                            previous = entry.previous!!.previous,
                            id = entry.previous!!.id,
                        )
                        else -> entry
                    }
                }
                is NavigationSegment.CombinedSegment -> entry
            }
        }
    val transformedCurrentEntryId = idsTransform.getValue(renderableNavigationState.navigationState.currentEntryId)

    val transformedBackstackState: BackstackState<NavigationSegment<T>> =
        object : BackstackState<NavigationSegment<T>> {
            override val entryMap: BackstackMap<NavigationSegment<T>>
                get() = transformedEntryMap
            override val currentEntryId: UUID
                get() = transformedCurrentEntryId
        }

    RenderableNavigationState(
        transformedBackstackState,
        transformedPaneMap,
    )
}

/**
 * The marker interface for a list entry.
 */
interface ListEntry : ListDetailInfo

/**
 * The marker interface for a detail entry.
 */
interface DetailEntry : ListDetailInfo

interface ListDetailInfo {
    val isListVisible: Boolean
    val isDetailVisible: Boolean
}

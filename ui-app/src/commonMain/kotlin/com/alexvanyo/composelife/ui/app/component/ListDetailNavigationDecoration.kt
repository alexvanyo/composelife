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
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.SegmentingNavigationDecoration
import java.util.UUID

/**
 * A [SegmentingNavigationDecoration] to display multiple panes in a list-detail layout, if there is enough room
 * to display both. If there isn't room to display both the list and the detail, then just one will be shown based
 * on the [ListEntry] and [DetailEntry]'s [ListDetailInfo].
 *
 * This decoration will only operate on entries of type [T] that implement [ListEntry] and [DetailEntry].
 *
 * This decoration works with the invariant that these entires are always paired, with a [ListEntry] _always_ being the
 * previous entry to the paired [DetailEntry].
 *
 * It is invalid for a [ListEntry] to be alone, or a [DetailEntry] to be alone - it is the responsibility of the
 * code maintaining the [BackstackState] to enforce this invariant.
 */
@Suppress("LongMethod")
fun <T> listDetailNavigationDecoration(
    onBackButtonPressed: () -> Unit,
): SegmentingNavigationDecoration<
    BackstackEntry<T>,
    BackstackState<T>,
    BackstackEntry<T>,
    BackstackState<T>,
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
        .filterValues { it.value !is ListEntry }
        .mapValues { (_, entry) ->
            when (entry.value) {
                is DetailEntry -> entry.previous!!.id
                else -> entry.id
            }
        }

    val transformedPaneMap: Map<UUID, @Composable () -> Unit> = entryMap
        .filterValues { it.value !is ListEntry }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailEntry) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (id, entry) ->
            key(id) {
                when (entry.value) {
                    is DetailEntry -> {
                        {
                            val previous = entry.previous
                            requireNotNull(previous)
                            val listEntry = previous.value as ListEntry
                            val detailEntry = entry.value as DetailEntry

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
                            // No-op transform for other entires
                            remember { movablePanes.getValue(entry.id) }.invoke()
                        }
                    }
                }
            }
        }

    val transformedEntryMap = entryMap
        .filterValues { it.value !is ListEntry }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailEntry) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (_, entry) ->
            if (entry.value is DetailEntry) {
                BackstackEntry(
                    entry.value,
                    previous = entry.previous!!.previous,
                    id = entry.previous!!.id,
                )
            } else {
                entry
            }
        }
    val transformedCurrentEntryId = idsTransform.getValue(renderableNavigationState.navigationState.currentEntryId)

    val transformedBackstackState: BackstackState<T> =
        object : BackstackState<T> {
            override val entryMap: BackstackMap<T>
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

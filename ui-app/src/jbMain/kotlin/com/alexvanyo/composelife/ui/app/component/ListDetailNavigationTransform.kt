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

import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationSegment
import com.alexvanyo.composelife.navigation.RenderableNavigationTransform
import com.alexvanyo.composelife.navigation.backstackRenderableNavigationTransform
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.trySharedElementWithCallerManagedVisibility
import kotlin.uuid.Uuid

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
@OptIn(ExperimentalSharedTransitionApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod")
fun <T> listDetailNavigationTransform(
    onBackButtonPressed: () -> Unit,
): RenderableNavigationTransform<
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    > =
    { renderableNavigationState ->
        /**
         * Create a mapping from each list entry ids in the navigation state to a unique pane id for the combination
         * list-detail panes.
         */
        val listDetailPaneIds = renderableNavigationState.navigationState
            .entryMap
            .entries
            .mapNotNull { entry ->
                when (val navigationSegment = entry.value.value) {
                    is NavigationSegment.CombinedSegment -> null
                    is NavigationSegment.SingleSegment -> {
                        when (navigationSegment.value) {
                            is ListEntry -> entry.key to key(entry.key) { remember { Uuid.random() } }
                            else -> null
                        }
                    }
                }
            }
            .toMap()

        val useListDetailPanes = renderableNavigationState.navigationState
            .entryMap
            .entries
            .mapNotNull { entry ->
                when (val navigationSegment = entry.value.value) {
                    is NavigationSegment.CombinedSegment -> null
                    is NavigationSegment.SingleSegment -> {
                        when (val value = navigationSegment.value) {
                            is ListDetailInfo -> {
                                key(entry.key) {
                                    val useListDetailPane by rememberUpdatedState(
                                        value.isListVisible && value.isDetailVisible,
                                    )

                                    entry.key to remember { { useListDetailPane } }
                                }
                            }
                            else -> null
                        }
                    }
                }
            }
            .toMap()

        backstackRenderableNavigationTransform<NavigationSegment<T>, NavigationSegment<T>> { entry, movablePanes ->
            when (val navigationSegment = entry.value) {
                is NavigationSegment.CombinedSegment -> entry to movablePanes.getValue(entry.id)
                is NavigationSegment.SingleSegment -> {
                    when (val value = navigationSegment.value) {
                        is ListEntry -> {
                            if (useListDetailPanes.getValue(entry.id).invoke()) {
                                null
                            } else {
                                entry to @Composable {
                                    val visible = !remember { useListDetailPanes.getValue(entry.id) }.invoke()

                                    Box(
                                        modifier = Modifier.trySharedElementWithCallerManagedVisibility(
                                            key = entry.id,
                                            visible = visible,
                                        ),
                                    ) {
                                        val pane = remember(entry.id) { movablePanes.getValue(entry.id) }
                                        if (visible) {
                                            pane.invoke()
                                        }
                                    }
                                }
                            }
                        }
                        is DetailEntry -> {
                            if (useListDetailPanes.getValue(entry.id).invoke()) {
                                val previous = requireNotNull(entry.previous)
                                val newEntryId = remember(previous.id) { listDetailPaneIds.getValue(previous.id) }

                                val newEntry = BackstackEntry(
                                    value = object : NavigationSegment.CombinedSegment<T> {
                                        override val combinedValues =
                                            previous.value.combinedValues + navigationSegment.combinedValues
                                    },
                                    previous = previous.previous,
                                    id = newEntryId,
                                )
                                val newPane = @Composable {
                                    @Suppress("UNCHECKED_CAST")
                                    val listEntry: ListEntry =
                                        (previous.value as NavigationSegment.SingleSegment<ListEntry>).value
                                    val detailEntry: DetailEntry = value

                                    ListDetailPaneScaffold(
                                        showList = listEntry.isListVisible,
                                        showDetail = detailEntry.isDetailVisible,
                                        listContent = {
                                            val visible = remember { useListDetailPanes.getValue(previous.id) }.invoke()

                                            Box(
                                                modifier = Modifier.trySharedElementWithCallerManagedVisibility(
                                                    key = previous.id,
                                                    visible = visible,
                                                ),
                                            ) {
                                                val pane = remember(previous.id) { movablePanes.getValue(previous.id) }
                                                if (visible) {
                                                    pane.invoke()
                                                }
                                            }
                                        },
                                        detailContent = {
                                            AnimatedContent(
                                                targetState = TargetState.Single(entry.id),
                                                animateInternalContentSizeChanges = false,
                                            ) { targetEntryId ->
                                                val visible = remember {
                                                    useListDetailPanes.getValue(
                                                        targetEntryId,
                                                    )
                                                }.invoke()

                                                Box(
                                                    modifier = Modifier.trySharedElementWithCallerManagedVisibility(
                                                        key = targetEntryId,
                                                        visible = visible,
                                                    ),
                                                ) {
                                                    val pane =
                                                        remember(targetEntryId) { movablePanes.getValue(targetEntryId) }
                                                    if (visible) {
                                                        pane.invoke()
                                                    }
                                                }
                                            }
                                        },
                                        onBackButtonPressed = onBackButtonPressed,
                                    )
                                }
                                newEntry to newPane
                            } else {
                                entry to @Composable {
                                    val visible = !remember { useListDetailPanes.getValue(entry.id) }.invoke()

                                    Box(
                                        modifier = Modifier.trySharedElementWithCallerManagedVisibility(
                                            key = entry.id,
                                            visible = visible,
                                        ),
                                    ) {
                                        val pane = remember(entry.id) { movablePanes.getValue(entry.id) }
                                        if (visible) {
                                            pane.invoke()
                                        }
                                    }
                                }
                            }
                        }
                        else -> entry to movablePanes.getValue(entry.id)
                    }
                }
            }
        }.invoke(renderableNavigationState)
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

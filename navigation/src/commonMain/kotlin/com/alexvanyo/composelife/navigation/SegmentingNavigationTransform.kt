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

import androidx.compose.runtime.remember
import java.util.UUID

/**
 * A [RenderableNavigationTransform] that segments an underlying navigation type into a [NavigationSegment].
 * Each value inside a [BackstackEntry] is wrapped into a [NavigationSegment.SingleSegment], with the same ids and
 * structure.
 */
fun <T> segmentingNavigationTransform(): RenderableNavigationTransform<
    BackstackEntry<T>,
    BackstackState<T>,
    BackstackEntry<NavigationSegment<T>>,
    BackstackState<NavigationSegment<T>>,
    > = { renderableNavigationState ->
    val entries = renderableNavigationState.navigationState.entryMap.values.toList()

    // Recursively create the transformed entries.
    val transformedEntryMap = remember(entries) {
        val map = mutableMapOf<UUID, BackstackEntry<NavigationSegment<T>>>()
        fun createNavigationSegment(entry: BackstackEntry<T>): BackstackEntry<NavigationSegment<T>> =
            map.getOrPut(entry.id) {
                BackstackEntry(
                    value = NavigationSegment.SingleSegment(entry.value),
                    previous = entry.previous?.let(::createNavigationSegment),
                    id = entry.id,
                )
            }

        entries.forEach(::createNavigationSegment)
        map
    }

    val transformedBackstackState: BackstackState<NavigationSegment<T>> =
        object : BackstackState<NavigationSegment<T>> {
            override val entryMap: BackstackMap<NavigationSegment<T>>
                get() = transformedEntryMap
            override val currentEntryId: UUID
                get() = renderableNavigationState.navigationState.currentEntryId
            override val previousEntryId: UUID?
                get() = renderableNavigationState.navigationState.previousEntryId
        }

    RenderableNavigationState(
        transformedBackstackState,
        renderableNavigationState.renderablePanes,
    )
}

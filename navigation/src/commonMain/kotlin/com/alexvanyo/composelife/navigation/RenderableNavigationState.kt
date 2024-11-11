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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import kotlin.uuid.Uuid

class RenderableNavigationState<T : NavigationEntry, S : NavigationState<T>>(
    val navigationState: S,
    val renderablePanes: Map<Uuid, @Composable () -> Unit>,
)

/**
 * A navigation transform from a [RenderableNavigationState] of [T1] and [S1] into a
 * [RenderableNavigationState] of [T2] and [S2].
 */
typealias RenderableNavigationTransform<T1, S1, T2, S2> =
    @Composable (RenderableNavigationState<T1, S1>) -> RenderableNavigationState<T2, S2>

/**
 * Returns a [RenderableNavigationTransform] that applies [entryTransform] to each entry.
 *
 * The order in which [entryTransform] is called for each entry is not guaranteed.
 */
fun <T1, T2> backstackRenderableNavigationTransform(
    /**
     * The transform to apply to each entry in [RenderableNavigationState], which is passed as [entry].
     *
     * The provided [movablePanes] is a map from the current entry ids to the pane content for each entry, pre-wrapped
     * in a [movableContentOf] to allow the content to be invoked in different places, or from the result from
     * different entry transforms.
     *
     * If this transform returns `null`, then this entry will not contribute to the resulting
     * [RenderableNavigationState], which can be useful if the pane for this entry is rendered as part of the result
     * for a different entry and this transform consolidates entries.
     *
     * The result can have a different entry value type, a different id space, and a different amount of entries.
     */
    entryTransform: @Composable (
        entry: BackstackEntry<T1>,
        movablePanes: Map<Uuid, @Composable () -> Unit>,
    ) -> BackstackRenderableNavigationTransformResult<T2>?,
): RenderableNavigationTransform<BackstackEntry<T1>, BackstackState<T1>, BackstackEntry<T2>, BackstackState<T2>> =
    { renderableNavigationState ->
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
        val transformed = renderableNavigationState.navigationState.entryMap.mapNotNull { (id, entry) ->
            key(id) {
                entryTransform(entry, movablePanes)?.let { id to it }
            }
        }.toMap()

        val transformedIdsMap = transformed.values.associateBy { it.id }

        val transformedEntryMap = remember(transformed) {
            val map = mutableMapOf<Uuid, BackstackEntry<T2>>()
            fun createNavigationSegment(
                result: BackstackRenderableNavigationTransformResult<T2>,
            ): BackstackEntry<T2> =
                map.getOrPut(result.id) {
                    BackstackEntry(
                        value = result.value,
                        previous = transformed[result.previousPreTransformedId]?.let(::createNavigationSegment),
                        id = result.id,
                    )
                }

            transformed.values.forEach(::createNavigationSegment)
            map
        }
        val transformedPaneMap = transformedIdsMap.mapValues { it.value.pane }

        val transformedCurrentEntryId =
            transformed.getValue(renderableNavigationState.navigationState.currentEntryId).id

        val transformedBackstackState: BackstackState<T2> =
            object : BackstackState<T2> {
                override val entryMap: BackstackMap<T2>
                    get() = transformedEntryMap
                override val currentEntryId: Uuid
                    get() = transformedCurrentEntryId
            }

        RenderableNavigationState(
            transformedBackstackState,
            transformedPaneMap,
        )
    }

/**
 * The result of the [entryTransform] for a [backstackRenderableNavigationTransform].
 */
class BackstackRenderableNavigationTransformResult<T>(
    /**
     * The transformed id of the entry.
     */
    val id: Uuid,
    /**
     * The transformed entry value of the entry.
     */
    val value: T,
    /**
     * The _non-transformed_ id of the transformed previous entry.
     */
    val previousPreTransformedId: Uuid?,
    /**
     * The transformed content pane for the entry.
     */
    val pane: @Composable () -> Unit,
)

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
import com.benasher44.uuid.Uuid

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

fun <T1, T2> backstackRenderableNavigationTransform(
    entryTransform: (
        BackstackEntry<T1>,
        movablePanes: Map<Uuid, @Composable () -> Unit>,
    ) -> Pair<BackstackEntry<T2>, @Composable () -> Unit>?,
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

        val transformedIdsMap = transformed.values.associateBy { it.first.id }
        val transformedEntryMap = transformedIdsMap.mapValues { it.value.first }
        val transformedPaneMap = transformedIdsMap.mapValues { it.value.second }

        val transformedCurrentEntryId =
            transformed.getValue(renderableNavigationState.navigationState.currentEntryId).first.id

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

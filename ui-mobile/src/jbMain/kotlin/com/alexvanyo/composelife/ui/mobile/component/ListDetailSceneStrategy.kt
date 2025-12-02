/*
 * Copyright 2025 The Android Open Source Project
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

import androidx.compose.runtime.Composable
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.scene.Scene
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.navigationEntry
import com.alexvanyo.composelife.navigation3.scene.SceneStrategy
import com.alexvanyo.composelife.navigation3.scene.SceneStrategyScope
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.TargetState

internal data class ListDetailPaneScene<T>(
    override val key: Any,
    val listEntry: NavEntry<BackstackEntry<T>>,
    val detailEntry: NavEntry<BackstackEntry<T>>,
    override val previousEntries: List<NavEntry<BackstackEntry<T>>>,
    val onBackButtonPressed: () -> Unit,
) : Scene<BackstackEntry<T>> {
    override val entries: List<NavEntry<BackstackEntry<T>>> = listOf(listEntry, detailEntry)

    override val content: @Composable () -> Unit = {
        ListDetailPaneScaffold(
            showList = (listEntry.navigationEntry.value as ListEntry).isListVisible,
            showDetail = (detailEntry.navigationEntry.value as DetailEntry).isDetailVisible,
            listContent = {
                listEntry.Content()
            },
            detailContent = {
                AnimatedContent(
                    targetState = TargetState.Single(detailEntry),
                    contentKey = { it.contentKey },
                    animateInternalContentSizeChanges = false,
                    label = "ListDetailPaneScene AnimatedContent",
                ) { targetDetailEntry ->
                    targetDetailEntry.Content()
                }
            },
            onBackButtonPressed = onBackButtonPressed,
        )
    }
}

class ListDetailSceneStrategy<T> : SceneStrategy<BackstackEntry<T>> {
    @Suppress("ReturnCount")
    override fun SceneStrategyScope<BackstackEntry<T>>.calculateScene(
        entries: List<NavEntry<BackstackEntry<T>>>,
    ): Scene<BackstackEntry<T>>? {
        val detailEntry = entries.lastOrNull()?.takeIf {
            val value = it.navigationEntry.value as? DetailEntry
            value != null && value.isDetailVisible
        } ?: return null
        val listEntry = entries.getOrNull(entries.size - 2)?.takeIf {
            val value = it.navigationEntry.value as? ListEntry
            value != null && value.isListVisible
        } ?: return null
        return ListDetailPaneScene(
            key = listEntry.contentKey,
            listEntry = listEntry,
            detailEntry = detailEntry,
            previousEntries = entries.dropLast(2),
            onBackButtonPressed = onBack,
        )
    }
}

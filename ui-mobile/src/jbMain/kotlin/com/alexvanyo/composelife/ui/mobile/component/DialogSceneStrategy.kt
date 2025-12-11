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

import androidx.compose.animation.SharedTransitionLayout
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.scene.OverlayScene
import androidx.navigation3.scene.Scene
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.LocalNavigationSharedTransitionScope
import com.alexvanyo.composelife.navigation.navigationEntry
import com.alexvanyo.composelife.navigation3.scene.SceneStrategy
import com.alexvanyo.composelife.navigation3.scene.SceneStrategyScope
import com.alexvanyo.composelife.ui.util.PlatformEdgeToEdgeDialog

internal data class DialogScene<T : Any>(
    override val key: Any,
    val wrappedScene: Scene<T>,
    val onBackButtonPressed: () -> Unit,
) : OverlayScene<T> {
    override val entries: List<NavEntry<T>> = wrappedScene.entries

    override val previousEntries: List<NavEntry<T>> = wrappedScene.previousEntries
    override val overlaidEntries: List<NavEntry<T>> = previousEntries

    override val content: @Composable () -> Unit = {
        PlatformEdgeToEdgeDialog(
            onDismissRequest = onBackButtonPressed,
        ) {
            SharedTransitionLayout {
                CompositionLocalProvider(LocalNavigationSharedTransitionScope provides null) {
                    wrappedScene.content()
                }
            }
        }
    }
}

class DialogSceneStrategy<T>(
    private val wrappedSceneStrategy: SceneStrategy<BackstackEntry<T>>,
) : SceneStrategy<BackstackEntry<T>> {
    @Suppress("ReturnCount")
    override fun SceneStrategyScope<BackstackEntry<T>>.calculateScene(
        entries: List<NavEntry<BackstackEntry<T>>>,
    ): Scene<BackstackEntry<T>>? {
        val wrappedScene = with(wrappedSceneStrategy) {
            calculateScene(entries) ?: return null
        }
        return if (wrappedScene.entries.all {
                (it.navigationEntry.value as? DialogableEntry)?.isDialog == true
            }) {
            DialogScene(
                key = wrappedScene.key,
                wrappedScene = wrappedScene,
                onBackButtonPressed = onBack,
            )
        } else {
            wrappedScene
        }
    }
}

interface DialogableEntry {
    val isDialog: Boolean
}

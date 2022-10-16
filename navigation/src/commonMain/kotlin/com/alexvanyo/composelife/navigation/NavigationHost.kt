/*
 * Copyright 2022 The Android Open Source Project
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

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedContentScope
import androidx.compose.animation.ContentTransform
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.scaleIn
import androidx.compose.animation.with
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import java.util.UUID

/**
 * The primary composable for displaying a [NavigationState].
 *
 * This automatically animated transitions between content, which is rendered for the current top-most entry with the
 * id of [NavigationState.currentEntryId] as specified in [content].
 *
 * The state for each entry is independently saved via [rememberSaveableStateHolder], and the corresponding state is
 * cleared when the keys are observed to no longer be in the backstack map.
 */
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun <T : NavigationEntry> NavigationHost(
    navigationState: NavigationState<T>,
    modifier: Modifier = Modifier,
    transitionSpec: AnimatedContentScope<T>.() -> ContentTransform = {
        fadeIn(animationSpec = tween(220, delayMillis = 90)) +
            scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90)) with
            fadeOut(animationSpec = tween(90))
    },
    contentAlignment: Alignment = Alignment.TopStart,
    content: @Composable (T) -> Unit,
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.map(UUID::toString) },
            restore = {
                mutableStateSetOf<UUID>().apply {
                    addAll(it.map(UUID::fromString))
                }
            },
        ),
    ) { mutableStateSetOf<UUID>() }

    AnimatedContent(
        targetState = navigationState.entryMap.getValue(navigationState.currentEntryId),
        transitionSpec = transitionSpec,
        contentAlignment = contentAlignment,
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet = navigationState.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
        (allKeys - keySet).forEach(stateHolder::removeState)
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.addAll(keySet)
    }
}

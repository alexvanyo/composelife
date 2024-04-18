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

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedContentTransitionScope
import androidx.compose.animation.ContentTransform
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.scaleIn
import androidx.compose.animation.togetherWith
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier

/**
 * The default [NavigationDecoration], which uses an [AnimatedContent] to animate between panes, using the given
 * [transitionSpec] and [contentAlignment].
 */
@Composable
fun <T : NavigationEntry> AnimatedContentNavigationDecoration(
    renderableNavigationState: RenderableNavigationState<T, NavigationState<T>>,
    modifier: Modifier = Modifier,
    transitionSpec: AnimatedContentTransitionScope<T>.() -> ContentTransform = {
        (
            fadeIn(animationSpec = tween(220, delayMillis = 90)) +
                scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90))
            )
            .togetherWith(fadeOut(animationSpec = tween(90)))
    },
    contentAlignment: Alignment = Alignment.TopStart,
) {
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

    AnimatedContent(
        targetState = renderableNavigationState.navigationState.currentEntry,
        transitionSpec = transitionSpec,
        contentAlignment = contentAlignment,
        contentKey = NavigationEntry::id,
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            // Fetch and store the movable pane to hold onto while animating out
            remember { movablePanes.getValue(entry.id) }.invoke()
        }
    }
}

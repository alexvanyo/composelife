/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.wear

import androidx.compose.animation.core.CubicBezierEasing
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.rememberTransition
import androidx.compose.animation.core.tween
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.drawWithContent
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.RectangleShape
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.platform.LocalConfiguration
import androidx.wear.compose.foundation.ExperimentalWearFoundationApi
import androidx.wear.compose.foundation.HierarchicalFocusCoordinator
import androidx.wear.compose.material.SwipeToDismissBox
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.MutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.associateWithRenderablePanes
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.previousEntry
import com.benasher44.uuid.uuid4

@Composable
fun <T> WearNavigationHost(
    navigationController: MutableBackstackNavigationController<T>,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) = WearNavigationHost(
    backstackState = navigationController,
    onNavigateBack = { navigationController.popBackstack() },
    modifier = modifier,
    content = content,
)

@Composable
fun <T> WearNavigationHost(
    backstackState: BackstackState<T>,
    onNavigateBack: () -> Unit,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) = WearNavigationFrame(
    renderableNavigationState = associateWithRenderablePanes(backstackState, content),
    onNavigateBack = onNavigateBack,
    modifier = modifier,
)

@OptIn(ExperimentalWearFoundationApi::class)
@Suppress("LongMethod")
@Composable
fun <T> WearNavigationFrame(
    renderableNavigationState: RenderableNavigationState<BackstackEntry<T>, BackstackState<T>>,
    onNavigateBack: () -> Unit,
    modifier: Modifier = Modifier,
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
    val currentEntry = renderableNavigationState.navigationState.currentEntry
    val previousEntry = renderableNavigationState.navigationState.previousEntry

    val foregroundTransition = renderableNavigationState.navigationState.entryMap.mapValues { (id, _) ->
        key(id) {
            val transitionState = remember {
                MutableTransitionState(id != currentEntry.id).apply {
                    targetState = true
                }
            }
            rememberTransition(transitionState)
        }
    }

    val isScreenRound = LocalConfiguration.current.isScreenRound

    SwipeToDismissBox(
        onDismissed = onNavigateBack,
        backgroundKey = previousEntry?.id ?: remember { uuid4() },
        contentKey = currentEntry.id,
        hasBackground = previousEntry != null,
        modifier = modifier,
    ) { isBackground ->
        val entry = if (isBackground) {
            checkNotNull(previousEntry) {
                "Current entry had no previous, should not be showing background!"
            }
        } else {
            currentEntry
        }

        val paneModifier = if (isBackground) {
            Modifier
        } else {
            val transition = foregroundTransition.getValue(entry.id)
            val animationSpec = remember { tween<Float>(400, easing = CubicBezierEasing(0.4f, 0f, 0.2f, 1f)) }
            val scale by transition.animateFloat(
                transitionSpec = { animationSpec },
                label = "scale",
            ) {
                if (it) 1f else 0.75f
            }
            val opacity by transition.animateFloat(
                transitionSpec = { animationSpec },
                label = "opacity",
            ) {
                if (it) 1f else 0.1f
            }
            val flashColorAlpha by transition.animateFloat(
                transitionSpec = { animationSpec },
                label = "flashColorAlpha",
            ) {
                if (it) 0f else 0.07f
            }
            Modifier
                .graphicsLayer {
                    scaleX = scale
                    scaleY = scale
                    alpha = opacity
                    clip = true
                    shape = if (isScreenRound) CircleShape else RectangleShape
                }
                .drawWithContent {
                    drawContent()
                    drawRect(Color.White.copy(alpha = flashColorAlpha))
                }
        }

        Box(modifier = paneModifier) {
            HierarchicalFocusCoordinator(
                requiresFocus = { currentEntry.id == entry.id },
            ) {
                key(entry.id) {
                    // Fetch and store the movable content to hold onto while animating out
                    val movablePane = remember { movablePanes.getValue(entry.id) }
                    movablePane()
                }
            }
        }
    }
}

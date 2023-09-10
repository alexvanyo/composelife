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

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationDecoration
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.previousEntry

@Composable
@Suppress("LongParameterList")
fun <T> PredictiveNavigationHost(
    predictiveBackState: PredictiveBackState,
    backstackState: BackstackState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) = NavigationHost(
    navigationState = backstackState,
    modifier = modifier,
    decoration = predictiveNavigationDecoration(
        predictiveBackState = predictiveBackState,
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
    ),
    content = content,
)

fun <T> predictiveNavigationDecoration(
    predictiveBackState: PredictiveBackState,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
): NavigationDecoration<BackstackEntry<out T>, BackstackState<T>> = { screen ->
    val currentScreen by rememberUpdatedState(screen)
    val movableScreens = entryMap.mapValues { (id, entry) ->
        key(id) {
            val currentEntry by rememberUpdatedState(entry)
            remember {
                movableContentOf {
                    currentScreen(currentEntry)
                }
            }
        }
    }

    AnimatedContent(
        targetState = when (predictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(currentEntry)
            is PredictiveBackState.Running -> {
                val previous = previousEntry
                if (previous != null) {
                    TargetState.InProgress(
                        current = currentEntry,
                        provisional = previous,
                        progress = predictiveBackState.progress,
                    )
                } else {
                    TargetState.Single(currentEntry)
                }
            }
        },
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
    ) { entry ->
        key(entry.id) {
            // Fetch and store the movable content to hold onto while animating out
            val movableScreen = remember { movableScreens.getValue(entry.id) }
            movableScreen()
        }
    }
}

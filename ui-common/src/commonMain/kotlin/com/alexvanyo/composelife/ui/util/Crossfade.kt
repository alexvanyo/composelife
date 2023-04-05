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

import androidx.compose.animation.core.EaseInOut
import androidx.compose.animation.core.Easing
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.updateTransition
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.graphicsLayer
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.onEach

/**
 * A version of Crossfade that can animate between [TargetState]s, a target of either one state or
 * between two states.
 */
@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun <T> Crossfade(
    targetState: TargetState<T>,
    modifier: Modifier = Modifier,
    alphaEasing: Easing = Easing({ 0f }, (0.5f to EaseInOut)),
    content: @Composable (T) -> Unit,
) {
    val previousTargetsInTransition = remember { mutableStateSetOf<T>() }

    val newTargetsInTransition = when (targetState) {
        is TargetState.InProgress -> setOf(targetState.current, targetState.provisional)
        is TargetState.Single -> setOf(targetState.current)
    }

    val currentTargetsInTransition = previousTargetsInTransition + newTargetsInTransition

    DisposableEffect(currentTargetsInTransition) {
        previousTargetsInTransition.addAll(currentTargetsInTransition)
        onDispose {}
    }

    val targetsWithTransitions = currentTargetsInTransition.associateWith { target ->
        key(target) {
            val targetAlpha = when (targetState) {
                is TargetState.InProgress -> when (target) {
                    targetState.provisional -> targetState.progress
                    targetState.current -> 1f - targetState.progress
                    else -> 0f
                }
                is TargetState.Single -> if (targetState.current == target) 1f else 0f
            }

            val transitionState = remember {
                MutableTransitionState(
                    initialState = if (previousTargetsInTransition.isEmpty()) {
                        targetAlpha
                    } else {
                        0f
                    },
                )
            }
            updateTransition(
                transitionState = transitionState.apply {
                    this.targetState = targetAlpha
                },
                label = "AnimatedContent",
            )
        }
    }

    targetsWithTransitions.forEach { (target, transition) ->
        if (
            when (targetState) {
                is TargetState.InProgress -> target != targetState.provisional && target != targetState.current
                is TargetState.Single -> target != targetState.current
            }
        ) {
            key(target) {
                LaunchedEffect(Unit) {
                    snapshotFlow { transition.currentState == transition.targetState }
                        .filter { it }
                        .onEach {
                            previousTargetsInTransition.remove(target)
                        }
                        .collect()
                }
            }
        }
    }

    Box(
        modifier = modifier,
        propagateMinConstraints = true,
    ) {
        targetsWithTransitions.forEach { (target, transition) ->
            key(target) {
                val smoothedAlpha by transition.animateFloat(
                    transitionSpec = { spring(stiffness = Spring.StiffnessMediumLow) },
                    label = "smoothedProgressToTarget",
                ) { alphaEasing.transform(it) }

                Box(
                    modifier = Modifier.graphicsLayer { alpha = smoothedAlpha },
                    propagateMinConstraints = true,
                ) {
                    content(target)
                }
            }
        }
    }
}

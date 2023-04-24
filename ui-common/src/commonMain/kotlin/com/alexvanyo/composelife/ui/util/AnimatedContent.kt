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
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.updateTransition
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.geometry.lerp
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.onEach

/**
 * A version of AnimatedContent that can animate between [TargetState]s, a target of either one state or
 * between two states.
 *
 * For all [content] that is not [TargetState.current], [LocalGhostElement] will be `true`.
 */
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
fun <T> AnimatedContent(
    targetState: TargetState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    alphaEasing: Easing = Easing({ 0f }, (0.5f to EaseInOut)),
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
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

    data class TargetStateLayoutId(val value: T)

    Layout(
        content = {
            targetsWithTransitions.forEach { (target, transition) ->
                key(target) {
                    /**
                     * Preserve the existing ghost element value, or if this is not the current value
                     */
                    val isGhostElement = LocalGhostElement.current || target != targetState.current
                    CompositionLocalProvider(LocalGhostElement provides isGhostElement) {
                        val smoothedAlpha by transition.animateFloat(
                            transitionSpec = { spring(stiffness = Spring.StiffnessMediumLow) },
                            label = "smoothedProgressToTarget",
                        ) { alphaEasing.transform(it) }

                        Box(
                            modifier = Modifier
                                .layoutId(TargetStateLayoutId(target))
                                .graphicsLayer { alpha = smoothedAlpha },
                            propagateMinConstraints = true,
                        ) {
                            content(target)
                        }
                    }
                }
            }
        },
        measurePolicy = { measurables, constraints ->
            val measurablesMap = measurables.associateBy {
                @Suppress("UNCHECKED_CAST")
                (it.layoutId as TargetStateLayoutId).value
            }

            val placeablesMaps = measurablesMap.mapValues { (_, measurable) ->
                measurable.measure(constraints)
            }

            val targetSize = when (targetState) {
                is TargetState.InProgress -> {
                    lerp(
                        placeablesMaps.getValue(targetState.current).size,
                        placeablesMaps.getValue(targetState.provisional).size,
                        targetState.progress,
                    )
                }
                is TargetState.Single -> placeablesMaps.getValue(targetState.current).size
            }

            layout(targetSize.width, targetSize.height) {
                placeablesMaps.values.forEach {
                    it.place(
                        contentAlignment.align(
                            size = it.size,
                            space = targetSize,
                            layoutDirection = layoutDirection,
                        ),
                    )
                }
            }
        },
        modifier = modifier.animateContentSize(
            animationSpec = contentSizeAnimationSpec,
            alignment = contentAlignment,
        ),
    )
}

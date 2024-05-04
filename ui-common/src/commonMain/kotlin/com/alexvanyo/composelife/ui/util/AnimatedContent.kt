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
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.Transition
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.tween
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.unit.IntSize

/**
 * A version of AnimatedContent that can animate between [TargetState]s, a target of either one state or
 * between two states.
 *
 * For all [content] that is not [TargetState.current], [LocalGhostElement] will be `true`.
 */
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
expect fun <T, M> AnimatedContent(
    targetState: TargetState<T, M>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    /**
     * A [Comparable] wrapper around a content, that is transitioning with the given [ContentStatus].
     *
     * By default, this performs a cross-fade between content.
     */
    transitionSpec: @Composable Transition<ContentStatus<M>>.(contentWithStatus: @Composable () -> Unit) -> Unit =
        { contentWithStatus ->
            val changingVisibilityEasing = Easing({ 0f }, (0.5f to EaseInOut))
            val alpha by animateFloat(
                transitionSpec = {
                    when (initialState) {
                        is ContentStatus.Appearing,
                        is ContentStatus.Disappearing,
                        -> spring()
                        ContentStatus.NotVisible,
                        ContentStatus.Visible,
                        -> when (this@animateFloat.targetState) {
                            is ContentStatus.Appearing,
                            is ContentStatus.Disappearing,
                            -> spring()
                            ContentStatus.NotVisible -> tween(durationMillis = 90)
                            ContentStatus.Visible -> tween(durationMillis = 220, delayMillis = 90)
                        }
                    }
                },
                label = "alpha",
            ) {
                when (it) {
                    is ContentStatus.Appearing -> changingVisibilityEasing.transform(it.progressToVisible)
                    is ContentStatus.Disappearing -> changingVisibilityEasing.transform(1f - it.progressToNotVisible)
                    ContentStatus.NotVisible -> 0f
                    ContentStatus.Visible -> 1f
                }
            }

            Box(
                modifier = Modifier.graphicsLayer { this.alpha = alpha },
                propagateMinConstraints = true,
            ) {
                contentWithStatus()
            }
        },
    /**
     * The [Comparator] governing the order in which targets are rendered.
     *
     * Targets will be rendered in ascending order, as given by the [targetRenderingComparator].
     *
     * By default, this will render the provisional target first (if any), then the current target, and then any
     * remaining targets.
     */
    targetRenderingComparator: Comparator<T> = compareBy {
        when (targetState) {
            is TargetState.InProgress -> when (it) {
                targetState.current -> 1f
                targetState.provisional -> 0f
                else -> 2f
            }
            is TargetState.Single -> if (it == targetState.current) 1f else 2f
        }
    },
    /**
     * The animation specification for animating the content size, if it is enabled.
     */
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    /**
     * Whether or not the content size animation should be run when the size of the content itself changes.
     * By default, this is `true`, which means that the size of the animated content container will animate if
     * the internal size of the content changes.
     * If this is `false`, only the size changes resulting from switching the [targetState] will be animated. Once the
     * target size has animated to a particular [targetState], that will "lock in" to that [targetState] size track,
     * size changes will be immediate when the [targetState] doesn't change.
     */
    animateInternalContentSizeChanges: Boolean = true,
    contentKey: (T) -> Any? = { it },
    content: @Composable (T) -> Unit,
)

sealed interface ContentStatus<out M> {
    data object Visible : ContentStatus<Nothing>
    data class Appearing<M>(
        val progressToVisible: Float,
        val metadata: M,
    ) : ContentStatus<M>
    data class Disappearing<M>(
        val progressToNotVisible: Float,
        val metadata: M,
    ) : ContentStatus<M>
    data object NotVisible : ContentStatus<Nothing>
}

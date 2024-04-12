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
import androidx.compose.animation.core.ExperimentalTransitionApi
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.Transition
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.rememberTransition
import androidx.compose.animation.core.snap
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.tween
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.runtime.snapshots.Snapshot
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.GraphicsLayerScope
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.AlignmentLine
import androidx.compose.ui.layout.IntrinsicMeasurable
import androidx.compose.ui.layout.IntrinsicMeasureScope
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.LayoutModifier
import androidx.compose.ui.layout.Measurable
import androidx.compose.ui.layout.MeasurePolicy
import androidx.compose.ui.layout.MeasureResult
import androidx.compose.ui.layout.MeasureScope
import androidx.compose.ui.layout.Placeable
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.util.fastMap
import com.alexvanyo.composelife.geometry.lerp
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.filter
import kotlinx.coroutines.flow.onEach

/**
 * A version of AnimatedContent that can animate between [TargetState]s, a target of either one state or
 * between two states.
 *
 * For all [content] that is not [TargetState.current], [LocalGhostElement] will be `true`.
 */
@OptIn(ExperimentalTransitionApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
fun <T, M> AnimatedContent(
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
) {
    val previousTargetsInTransition = remember { mutableStateMapOf<Any?, T>() }

    val newTargetsInTransition = when (targetState) {
        is TargetState.InProgress -> setOf(targetState.current, targetState.provisional)
        is TargetState.Single -> setOf(targetState.current)
    }.associateBy(contentKey)

    val currentTargetsInTransition = previousTargetsInTransition + newTargetsInTransition

    DisposableEffect(currentTargetsInTransition) {
        previousTargetsInTransition.putAll(currentTargetsInTransition)
        onDispose {}
    }

    val targetKeyState = targetState.map(contentKey)

    val targetKeysWithTransitions = currentTargetsInTransition.keys.associateWith { targetKey ->
        key(targetKey) {
            val targetContentStatus = when (targetKeyState) {
                is TargetState.InProgress -> when (targetKey) {
                    targetKeyState.provisional -> ContentStatus.Appearing(
                        progressToVisible = targetKeyState.progress,
                        metadata = targetKeyState.metadata,
                    )
                    targetKeyState.current -> ContentStatus.Disappearing(
                        progressToNotVisible = targetKeyState.progress,
                        metadata = targetKeyState.metadata,
                    )
                    else -> ContentStatus.NotVisible
                }
                is TargetState.Single -> if (targetKeyState.current == targetKey) {
                    ContentStatus.Visible
                } else {
                    ContentStatus.NotVisible
                }
            }

            val transitionState = remember {
                MutableTransitionState(
                    initialState = if (previousTargetsInTransition.isEmpty()) {
                        targetContentStatus
                    } else {
                        ContentStatus.NotVisible
                    },
                )
            }
            rememberTransition(
                transitionState = transitionState.apply {
                    this.targetState = targetContentStatus
                },
                label = "Content Status",
            )
        }
    }

    targetKeysWithTransitions.forEach { (targetKey, transition) ->
        if (
            when (targetKeyState) {
                is TargetState.InProgress ->
                    targetKey != targetKeyState.provisional && targetKey != targetKeyState.current
                is TargetState.Single ->
                    targetKey != targetKeyState.current
            }
        ) {
            key(targetKey) {
                LaunchedEffect(Unit) {
                    snapshotFlow { transition.currentState == transition.targetState }
                        .filter { it }
                        .onEach {
                            previousTargetsInTransition.remove(targetKey)
                        }
                        .collect()
                }
            }
        }
    }

    data class ConstraintsType(
        val isLookahead: Boolean,
    )

    @Stable
    class ConstraintsCache {
        val cache = mutableStateMapOf<ConstraintsType, Constraints>()
    }

    val targetsWithConstraints: Map<Any?, ConstraintsCache> =
        currentTargetsInTransition.keys.associateWith { targetKey ->
            key(targetKey) {
                remember { ConstraintsCache() }
            }
        }

    data class TargetStateLayoutId(val value: T)

    var completedTargetSizeAnimation by remember(targetKeyState) {
        mutableStateOf(true)
    }

    Layout(
        content = {
            targetKeysWithTransitions.forEach { (targetKey, transition) ->
                val target = currentTargetsInTransition.getValue(targetKey)
                key(targetKey) {
                    /**
                     * Preserve the existing ghost element value, or if this is not the current value
                     */
                    val isGhostElement = LocalGhostElement.current ||
                        contentKey(target) != contentKey(targetState.current)
                    CompositionLocalProvider(LocalGhostElement provides isGhostElement) {
                        Box(
                            modifier = Modifier.layoutId(TargetStateLayoutId(target)),
                            propagateMinConstraints = true,
                        ) {
                            transition.transitionSpec {
                                content(target)
                            }
                        }
                    }
                }
            }
        },
        measurePolicy = object : MeasurePolicy {

            private fun MeasureScope.measure(
                measurables: List<Measurable>,
                constraints: Constraints,
                isIntrinsic: Boolean,
            ): MeasureResult {
                val measurablesMap = measurables.associateBy {
                    @Suppress("UNCHECKED_CAST")
                    (it.layoutId as TargetStateLayoutId).value
                }

                val constraintsType = ConstraintsType(
                    isLookahead = isLookingAhead,
                )
                val placeablesMap = measurablesMap.mapValues { (target, measurable) ->
                    // Determine the contraints to measure with
                    val resolvedConstraints = if (isIntrinsic) {
                        // If this is an intrinsic measurement, the constraints have no external dependency, so we
                        // don't need to cache them.
                        constraints
                    } else {
                        // For safety, we don't want to create an infinite measurement loop if this method happens
                        // to run multiple times with different constraints for the same ConstraintsType.
                        // To accomplish that, don't observe reads here
                        Snapshot.withoutReadObservation {
                            // Get the cache for the given target
                            val cache = targetsWithConstraints.getValue(contentKey(target)).cache

                            // If we don't have a saved constraints, the target is the current target, or the
                            // target is the provisional target, update the constraints. Otherwise, we measure using
                            // the cached constraints as we animate out.
                            @Suppress("ComplexCondition")
                            if (constraintsType !in cache ||
                                contentKey(target) == targetKeyState.current ||
                                (
                                    targetKeyState.isInProgress() &&
                                        contentKey(target) == targetKeyState.provisional
                                    )
                            ) {
                                cache[constraintsType] = constraints
                            }
                            cache.getValue(constraintsType)
                        }
                    }

                    measurable.measure(resolvedConstraints)
                }

                val targetSize = when (targetState) {
                    is TargetState.InProgress -> {
                        lerp(
                            placeablesMap.getValue(targetState.current).size,
                            placeablesMap.getValue(targetState.provisional).size,
                            targetState.progress,
                        )
                    }
                    is TargetState.Single -> placeablesMap.getValue(targetState.current).size
                }

                return layout(targetSize.width, targetSize.height) {
                    placeablesMap.entries
                        .sortedWith(
                            Comparator.comparing(
                                Map.Entry<T, Placeable>::key,
                                targetRenderingComparator,
                            ),
                        )
                        .forEach { (_, placeable) ->
                            placeable.place(
                                contentAlignment.align(
                                    size = placeable.size,
                                    space = targetSize,
                                    layoutDirection = layoutDirection,
                                ),
                            )
                        }
                }
            }

            override fun MeasureScope.measure(
                measurables: List<Measurable>,
                constraints: Constraints,
            ): MeasureResult =
                measure(
                    measurables = measurables,
                    constraints = constraints,
                    isIntrinsic = false,
                )

            override fun IntrinsicMeasureScope.maxIntrinsicHeight(
                measurables: List<IntrinsicMeasurable>,
                width: Int,
            ): Int {
                val mapped = measurables.fastMap {
                    DefaultIntrinsicMeasurable(it, IntrinsicMinMax.Max, IntrinsicWidthHeight.Height)
                }
                val constraints = Constraints(maxWidth = width)
                val layoutReceiver = IntrinsicsMeasureScope(this, layoutDirection)
                val layoutResult = layoutReceiver.measure(
                    measurables = mapped,
                    constraints = constraints,
                    isIntrinsic = true,
                )
                return layoutResult.height
            }

            override fun IntrinsicMeasureScope.maxIntrinsicWidth(
                measurables: List<IntrinsicMeasurable>,
                height: Int,
            ): Int {
                val mapped = measurables.fastMap {
                    DefaultIntrinsicMeasurable(it, IntrinsicMinMax.Max, IntrinsicWidthHeight.Width)
                }
                val constraints = Constraints(maxHeight = height)
                val layoutReceiver = IntrinsicsMeasureScope(this, layoutDirection)
                val layoutResult = layoutReceiver.measure(
                    measurables = mapped,
                    constraints = constraints,
                    isIntrinsic = true,
                )
                return layoutResult.width
            }

            override fun IntrinsicMeasureScope.minIntrinsicHeight(
                measurables: List<IntrinsicMeasurable>,
                width: Int,
            ): Int {
                val mapped = measurables.fastMap {
                    DefaultIntrinsicMeasurable(it, IntrinsicMinMax.Min, IntrinsicWidthHeight.Height)
                }
                val constraints = Constraints(maxWidth = width)
                val layoutReceiver = IntrinsicsMeasureScope(this, layoutDirection)
                val layoutResult = layoutReceiver.measure(
                    measurables = mapped,
                    constraints = constraints,
                    isIntrinsic = true,
                )
                return layoutResult.height
            }

            override fun IntrinsicMeasureScope.minIntrinsicWidth(
                measurables: List<IntrinsicMeasurable>,
                height: Int,
            ): Int {
                val mapped = measurables.fastMap {
                    DefaultIntrinsicMeasurable(it, IntrinsicMinMax.Min, IntrinsicWidthHeight.Width)
                }
                val constraints = Constraints(maxHeight = height)
                val layoutReceiver = IntrinsicsMeasureScope(this, layoutDirection)
                val layoutResult = layoutReceiver.measure(
                    measurables = mapped,
                    constraints = constraints,
                    isIntrinsic = true,
                )
                return layoutResult.width
            }
        },
        modifier = modifier.animateContentSize(
            // If we have completed animating the size of the target state, and we don't want to animate internal
            // content size changes, we've now "locked in" to the track of this specific target state, so start
            // snapping to the content size
            animationSpec = if (completedTargetSizeAnimation && !animateInternalContentSizeChanges) {
                snap()
            } else {
                contentSizeAnimationSpec
            },
            alignment = contentAlignment,
            finishedListener = { _, _ ->
                completedTargetSizeAnimation = true
            },
        ),
    )
}

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

// Adapted from MeasurePolicy.kt

/**
 * Used to return a fixed sized item for intrinsics measurements in [Layout]
 */
private class FixedSizeIntrinsicsPlaceable(width: Int, height: Int) : Placeable() {
    init {
        measuredSize = IntSize(width, height)
    }

    override fun get(alignmentLine: AlignmentLine): Int = AlignmentLine.Unspecified
    override fun placeAt(
        position: IntOffset,
        zIndex: Float,
        layerBlock: (GraphicsLayerScope.() -> Unit)?,
    ) = Unit
}

/**
 * Identifies an [IntrinsicMeasurable] as a min or max intrinsic measurement.
 */
private enum class IntrinsicMinMax {
    Min, Max
}

/**
 * Identifies an [IntrinsicMeasurable] as a width or height intrinsic measurement.
 */
private enum class IntrinsicWidthHeight {
    Width, Height
}

/**
 * A wrapper around a [Measurable] for intrinsic measurements in [Layout]. Consumers of
 * [Layout] don't identify intrinsic methods, but we can give a reasonable implementation
 * by using their [measure], substituting the intrinsics gathering method
 * for the [Measurable.measure] call.
 */
private class DefaultIntrinsicMeasurable(
    val measurable: IntrinsicMeasurable,
    val minMax: IntrinsicMinMax,
    val widthHeight: IntrinsicWidthHeight,
) : Measurable {
    override val parentData: Any?
        get() = measurable.parentData

    override fun measure(constraints: Constraints): Placeable {
        if (widthHeight == IntrinsicWidthHeight.Width) {
            val width = if (minMax == IntrinsicMinMax.Max) {
                measurable.maxIntrinsicWidth(constraints.maxHeight)
            } else {
                measurable.minIntrinsicWidth(constraints.maxHeight)
            }
            return FixedSizeIntrinsicsPlaceable(width, constraints.maxHeight)
        }
        val height = if (minMax == IntrinsicMinMax.Max) {
            measurable.maxIntrinsicHeight(constraints.maxWidth)
        } else {
            measurable.minIntrinsicHeight(constraints.maxWidth)
        }
        return FixedSizeIntrinsicsPlaceable(constraints.maxWidth, height)
    }

    override fun minIntrinsicWidth(height: Int): Int {
        return measurable.minIntrinsicWidth(height)
    }

    override fun maxIntrinsicWidth(height: Int): Int {
        return measurable.maxIntrinsicWidth(height)
    }

    override fun minIntrinsicHeight(width: Int): Int {
        return measurable.minIntrinsicHeight(width)
    }

    override fun maxIntrinsicHeight(width: Int): Int {
        return measurable.maxIntrinsicHeight(width)
    }
}

/**
 * Receiver scope for [Layout]'s and [LayoutModifier]'s layout lambda when used in an intrinsics
 * call.
 */
private class IntrinsicsMeasureScope(
    density: Density,
    override val layoutDirection: LayoutDirection,
) : MeasureScope, Density by density

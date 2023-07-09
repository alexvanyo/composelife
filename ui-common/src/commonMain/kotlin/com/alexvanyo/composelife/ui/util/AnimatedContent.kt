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
import androidx.compose.animation.core.snap
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.updateTransition
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
import androidx.compose.ui.ExperimentalComposeUiApi
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
@OptIn(ExperimentalComposeUiApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
fun <T> AnimatedContent(
    targetState: TargetState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    alphaEasing: Easing = Easing({ 0f }, (0.5f to EaseInOut)),
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

    data class ConstraintsType(
        val isLookahead: Boolean,
    )

    @Stable
    class ConstraintsCache {
        val cache = mutableStateMapOf<ConstraintsType, Constraints>()
    }

    val targetsWithConstraints: Map<T, ConstraintsCache> =
        currentTargetsInTransition.associateWith { target ->
            key(target) {
                remember { ConstraintsCache() }
            }
        }

    data class TargetStateLayoutId(val value: T)

    var completedTargetSizeAnimation by remember(targetState) {
        mutableStateOf(false)
    }

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
                            label = "smoothedAlpha",
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
                    isLookahead = isLookingAhead(),
                )
                val placeablesMaps = measurablesMap.mapValues { (target, measurable) ->
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
                            val cache = targetsWithConstraints.getValue(target).cache

                            // If we don't have a saved constraints, the target is the current target, or the
                            // target is the provisional target, update the constraints. Otherwise, we measure using
                            // the cached constraints as we animate out.
                            @Suppress("ComplexCondition")
                            if (constraintsType !in cache ||
                                target == targetState.current ||
                                (targetState.isInProgress() && target == targetState.provisional)
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
                            placeablesMaps.getValue(targetState.current).size,
                            placeablesMaps.getValue(targetState.provisional).size,
                            targetState.progress,
                        )
                    }
                    is TargetState.Single -> placeablesMaps.getValue(targetState.current).size
                }

                return layout(targetSize.width, targetSize.height) {
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

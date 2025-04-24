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
import androidx.compose.animation.core.animateDp
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.tween
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.RoundRect
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.geometry.toRect
import androidx.compose.ui.graphics.Outline
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.graphics.Shape
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.graphics.copy
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.onLayoutRectChanged
import androidx.compose.ui.spatial.RelativeLayoutBounds
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.lerp
import androidx.compose.ui.unit.toOffset
import androidx.compose.ui.util.lerp
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.associateWithRenderablePanes
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.previousEntry

@Composable
@Suppress("LongParameterList")
fun <T> MaterialPredictiveNavigationHost(
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    backstackState: BackstackState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
    clipUsingWindowShape: Boolean = false,
    content: @Composable (BackstackEntry<T>) -> Unit,
) = MaterialPredictiveNavigationFrame(
    renderableNavigationState = associateWithRenderablePanes(backstackState, content),
    modifier = modifier,
    repeatablePredictiveBackState = repeatablePredictiveBackState,
    contentAlignment = contentAlignment,
    contentSizeAnimationSpec = contentSizeAnimationSpec,
    animateInternalContentSizeChanges = animateInternalContentSizeChanges,
    clipUsingWindowShape = clipUsingWindowShape,
)

@Suppress("LongParameterList")
@Composable
fun <T> CrossfadePredictiveNavigationFrame(
    renderableNavigationState: RenderableNavigationState<BackstackEntry<T>, BackstackState<T>>,
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
) {
    val rememberedPanes = renderableNavigationState.renderablePanes.mapValues { (id, paneContent) ->
        key(id) {
            rememberUpdatedState(paneContent)
        }
    }

    val backstackState = renderableNavigationState.navigationState
    val targetState = when (repeatablePredictiveBackState) {
        RepeatablePredictiveBackState.NotRunning -> TargetState.Single(backstackState.currentEntry)
        is RepeatablePredictiveBackState.Running -> {
            val previous = backstackState.previousEntry
            if (previous != null) {
                TargetState.InProgress(
                    current = backstackState.currentEntry,
                    provisional = previous,
                    progress = repeatablePredictiveBackState.progress,
                )
            } else {
                TargetState.Single(backstackState.currentEntry)
            }
        }
    }

    AnimatedContent(
        targetState = targetState,
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        contentKey = BackstackEntry<T>::id,
        label = "CrossfadePredictiveNavigationFrame",
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            remember { rememberedPanes.getValue(entry.id) }.value.invoke()
        }
    }
}

/**
 * A navigation frame that implements the Material predictive back design for animating between panes upon
 * popping.
 *
 * https://developer.android.com/design/ui/mobile/guides/patterns/predictive-back#full-pane-surfaces
 */
@Suppress("CyclomaticComplexMethod", "LongMethod", "LongParameterList")
@Composable
fun <T> MaterialPredictiveNavigationFrame(
    renderableNavigationState: RenderableNavigationState<BackstackEntry<T>, BackstackState<T>>,
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
    clipUsingWindowShape: Boolean = false,
) {
    val rememberedPanes = renderableNavigationState.renderablePanes.mapValues { (id, paneContent) ->
        key(id) {
            rememberUpdatedState(paneContent)
        }
    }

    val backstackState = renderableNavigationState.navigationState

    val targetState = when (repeatablePredictiveBackState) {
        RepeatablePredictiveBackState.NotRunning -> TargetState.Single(backstackState.currentEntry)
        is RepeatablePredictiveBackState.Running -> {
            val previous = backstackState.previousEntry
            if (previous != null) {
                TargetState.InProgress(
                    current = backstackState.currentEntry,
                    provisional = previous,
                    progress = repeatablePredictiveBackState.progress,
                    metadata = repeatablePredictiveBackState,
                )
            } else {
                TargetState.Single(backstackState.currentEntry)
            }
        }
    }

    AnimatedContent(
        targetState = targetState,
        contentAlignment = contentAlignment,
        transitionSpec = { contentWithStatus ->
            val contentStatusTargetState = this@AnimatedContent.targetState

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
                    is ContentStatus.Appearing -> 1f
                    is ContentStatus.Disappearing -> 1f
                    ContentStatus.NotVisible -> 0f
                    ContentStatus.Visible -> 1f
                }
            }
            val lastDisappearingValue by remember {
                mutableStateOf<ContentStatus.Disappearing<out RepeatablePredictiveBackState.Running>?>(null)
            }.apply {
                when (contentStatusTargetState) {
                    is ContentStatus.Appearing -> value = null
                    is ContentStatus.Disappearing -> if (contentStatusTargetState.progressToNotVisible >= 0.01f) {
                        // Only save that we were disappearing if the progress is at least 1% along
                        value = contentStatusTargetState
                    }
                    ContentStatus.NotVisible -> Unit // Preserve the previous value of wasDisappearing
                    ContentStatus.Visible -> value = null
                }
            }
            val scale by animateFloat(
                label = "scale",
            ) {
                when (it) {
                    is ContentStatus.Appearing -> 1f
                    is ContentStatus.Disappearing -> lerp(1f, 0.9f, it.progressToNotVisible)
                    ContentStatus.NotVisible -> if (lastDisappearingValue != null) 0.9f else 1f
                    ContentStatus.Visible -> 1f
                }
            }
            val translationX by animateDp(
                label = "translationX",
            ) {
                when (it) {
                    is ContentStatus.Appearing -> 0.dp
                    is ContentStatus.Disappearing -> {
                        val metadata = it.metadata
                        lerp(
                            0.dp,
                            8.dp,
                            it.progressToNotVisible,
                        ) * when (metadata.backEventEdge) {
                            BackEventEdge.None -> 0f
                            BackEventEdge.Left -> -1f
                            BackEventEdge.Right -> 1f
                        }
                    }
                    ContentStatus.NotVisible -> {
                        8.dp * when (lastDisappearingValue?.metadata?.backEventEdge) {
                            null, BackEventEdge.None -> 0f
                            BackEventEdge.Left -> -1f
                            BackEventEdge.Right -> 1f
                        }
                    }
                    ContentStatus.Visible -> 0.dp
                }
            }
            val cornerRadius by animateDp(
                label = "cornerRadius",
            ) {
                when (it) {
                    is ContentStatus.Appearing -> 0.dp
                    is ContentStatus.Disappearing -> lerp(0.dp, 28.dp, it.progressToNotVisible)
                    ContentStatus.NotVisible -> if (lastDisappearingValue != null) 28.dp else 0.dp
                    ContentStatus.Visible -> 0.dp
                }
            }
            val pivotFractionX by animateFloat(
                label = "pivotFractionX",
            ) {
                when (it) {
                    is ContentStatus.Appearing -> 0.5f
                    is ContentStatus.Disappearing -> {
                        when (it.metadata.backEventEdge) {
                            BackEventEdge.None -> 0.5f
                            BackEventEdge.Left -> 1f
                            BackEventEdge.Right -> 0f
                        }
                    }
                    ContentStatus.NotVisible -> {
                        when (lastDisappearingValue?.metadata?.backEventEdge) {
                            null, BackEventEdge.None -> 0.5f
                            BackEventEdge.Left -> 1f
                            BackEventEdge.Right -> 0f
                        }
                    }
                    ContentStatus.Visible -> 0.5f
                }
            }

            val windowShape = currentWindowShape()
            var relativeLayoutBounds: RelativeLayoutBounds? by remember { mutableStateOf(null) }

            Box(
                modifier = Modifier
                    .onLayoutRectChanged(
                        throttleMillis = 0,
                        debounceMillis = 0,
                    ) {
                        relativeLayoutBounds = it
                    }
                    .graphicsLayer {
                        shape = if (clipUsingWindowShape) {
                            val cornerRadiusPath = Path().apply {
                                addRoundRect(
                                    RoundRect(size.toRect(), CornerRadius(cornerRadius.toPx()))
                                )
                            }
                            val clippingPath = cornerRadiusPath and windowShape.path.copy().apply {
                                translate(-(relativeLayoutBounds?.positionInWindow?.toOffset() ?: Offset.Zero))
                            }
                            object : Shape {
                                override fun createOutline(
                                    size: Size,
                                    layoutDirection: LayoutDirection,
                                    density: Density,
                                ): Outline = Outline.Generic(clippingPath)
                            }
                        } else {
                            RoundedCornerShape(cornerRadius)
                        }
                        shadowElevation = 6.dp.toPx()
                        this.translationX = translationX.toPx()
                        this.alpha = alpha
                        this.scaleX = scale
                        this.scaleY = scale
                        this.transformOrigin = TransformOrigin(pivotFractionX, 0.5f)
                        clip = true
                    },
                propagateMinConstraints = true,
            ) {
                contentWithStatus()
            }
        },
        targetRenderingComparator = compareByDescending { entry ->
            // Render items in order of the backstack, with the top of the backstack rendered last
            // If the entry is not in the backstack at all, assume that it is disappearing aftering being popped, and
            // render it on top of everything still in the backstack
            generateSequence(
                backstackState.currentEntry,
                BackstackEntry<T>::previous,
            ).indexOfFirst { it.id == entry.id }
        },
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        contentKey = BackstackEntry<T>::id,
        label = "MaterialPredictiveNavigationFrame",
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            remember { rememberedPanes.getValue(entry.id) }.value.invoke()
        }
    }
}

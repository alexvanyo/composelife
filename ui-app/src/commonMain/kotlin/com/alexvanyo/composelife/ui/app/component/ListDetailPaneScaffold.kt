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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.animation.animateColorAsState
import androidx.compose.animation.core.animateDp
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.animateFloat
import androidx.compose.animation.core.exponentialDecay
import androidx.compose.animation.core.spring
import androidx.compose.animation.core.tween
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.gestures.Orientation
import androidx.compose.foundation.gestures.anchoredDraggable
import androidx.compose.foundation.hoverable
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.interaction.collectIsDraggedAsState
import androidx.compose.foundation.interaction.collectIsHoveredAsState
import androidx.compose.foundation.interaction.collectIsPressedAsState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.only
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsEndWidth
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsStartWidth
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.PointerIcon
import androidx.compose.ui.input.pointer.pointerHoverIcon
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.lerp
import androidx.compose.ui.util.lerp
import com.alexvanyo.composelife.ui.util.AnchoredDraggableState
import com.alexvanyo.composelife.ui.util.AnchoredDraggableStateSaver
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.ContentStatus
import com.alexvanyo.composelife.ui.util.DraggableAnchors
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackHandler
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackState
import com.alexvanyo.composelife.ui.util.SwipeEdge
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.asFoundationDraggableAnchors
import com.alexvanyo.composelife.ui.util.rememberRepeatablePredictiveBackStateHolder
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.SealedEnum
import kotlin.math.roundToInt

@OptIn(ExperimentalFoundationApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
fun ListDetailPaneScaffold(
    showList: Boolean,
    showDetail: Boolean,
    listContent: @Composable () -> Unit,
    detailContent: @Composable () -> Unit,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val showListAndDetail = showList && showDetail

    val predictiveBackStateHolder = rememberRepeatablePredictiveBackStateHolder()
    RepeatablePredictiveBackHandler(
        repeatablePredictiveBackStateHolder = predictiveBackStateHolder,
        enabled = showDetail && !showList,
    ) {
        onBackButtonPressed()
    }

    val density = LocalDensity.current
    val anchoredDraggableState = rememberSaveable(
        saver = AnchoredDraggableStateSaver(
            positionalThreshold = { totalDistance -> totalDistance * 0.5f },
            velocityThreshold = { with(density) { 200.dp.toPx() } },
            snapAnimationSpec = spring(),
            decayAnimationSpec = exponentialDecay(),
        ),
    ) {
        AnchoredDraggableState(
            initialValue = 0.5f,
            positionalThreshold = { totalDistance -> totalDistance * 0.5f },
            velocityThreshold = { with(density) { 200.dp.toPx() } },
            snapAnimationSpec = spring(),
            decayAnimationSpec = exponentialDecay(),
        )
    }

    val minPaneWidth = 200.dp

    Surface(
        modifier = modifier,
    ) {
        if (showListAndDetail) {
            Layout(
                layoutIdTypes = ListAndDetailLayoutTypes._sealedEnum,
                content = {
                    Spacer(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.StartInsets)
                            .windowInsetsStartWidth(WindowInsets.safeDrawing),
                    )
                    Spacer(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.EndInsets)
                            .windowInsetsEndWidth(WindowInsets.safeDrawing),
                    )

                    Box(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.List)
                            .consumeWindowInsets(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.End,
                                ),
                            ),
                    ) {
                        listContent()
                    }

                    Column(
                        Modifier
                            .layoutId(ListAndDetailLayoutTypes.Detail)
                            .consumeWindowInsets(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Start,
                                ),
                            )
                            .windowInsetsPadding(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Horizontal,
                                ),
                            )
                            .padding(
                                top = 4.dp,
                                start = 8.dp,
                                end = 8.dp,
                                bottom = 16.dp,
                            ),
                    ) {
                        Spacer(Modifier.windowInsetsTopHeight(WindowInsets.safeDrawing))
                        Surface(
                            color = MaterialTheme.colorScheme.secondaryContainer,
                            shape = RoundedCornerShape(16.dp),
                            modifier = Modifier
                                .weight(1f)
                                .consumeWindowInsets(
                                    WindowInsets.safeDrawing.only(
                                        WindowInsetsSides.Vertical,
                                    ),
                                ),
                        ) {
                            detailContent()
                        }
                        Spacer(Modifier.windowInsetsBottomHeight(WindowInsets.safeDrawing))
                    }

                    Box(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.Divider)
                            .fillMaxHeight()
                            .windowInsetsPadding(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Vertical,
                                ),
                            ),
                        contentAlignment = Alignment.Center,
                    ) {
                        val handleInteractionSource = remember { MutableInteractionSource() }

                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .hoverable(
                                    interactionSource = handleInteractionSource,
                                )
                                .anchoredDraggable(
                                    state = anchoredDraggableState,
                                    orientation = Orientation.Horizontal,
                                    interactionSource = handleInteractionSource,
                                )
                                .pointerHoverIcon(PointerIcon.Hand),
                            contentAlignment = Alignment.Center,
                        ) {
                            val isHandleDragged by handleInteractionSource.collectIsDraggedAsState()
                            val isHandleHovered by handleInteractionSource.collectIsHoveredAsState()
                            val isHandlePressed by handleInteractionSource.collectIsPressedAsState()
                            val isHandleActive = isHandleDragged || isHandleHovered || isHandlePressed
                            val handleWidth by animateDpAsState(
                                targetValue = if (isHandleActive) 12.dp else 4.dp,
                                label = "handleWidth",
                            )
                            val handleColor by animateColorAsState(
                                targetValue = if (isHandleActive) {
                                    MaterialTheme.colorScheme.onSurface
                                } else {
                                    MaterialTheme.colorScheme.outline
                                },
                                label = "handleColor",
                            )
                            Canvas(
                                modifier = Modifier.fillMaxSize(),
                            ) {
                                val handleSize = DpSize(handleWidth, 48.dp).toSize()
                                val handleOffset = Offset(
                                    (size.width - handleSize.width) / 2f,
                                    (size.height - handleSize.height) / 2f,
                                )
                                drawRoundRect(
                                    color = handleColor,
                                    topLeft = handleOffset,
                                    size = handleSize,
                                    cornerRadius = CornerRadius(handleSize.width / 2),
                                )
                            }
                        }
                    }
                },
                measurePolicy = { measurables, constraints ->
                    val startInsetsPlaceable = measurables
                        .getValue(ListAndDetailLayoutTypes.StartInsets)
                        .measure(constraints.copy(minWidth = 0))

                    val endInsetsPlaceable = measurables
                        .getValue(ListAndDetailLayoutTypes.EndInsets)
                        .measure(constraints.copy(minWidth = 0))

                    val minPaneWidthPx = minPaneWidth.toPx()

                    val freeSpace = constraints.maxWidth -
                        startInsetsPlaceable.width -
                        endInsetsPlaceable.width -
                        minPaneWidthPx * 2

                    layout(constraints.maxWidth, constraints.maxHeight) {
                        val minAnchoredDraggablePosition = 0f
                        val maxAnchoredDraggablePosition = freeSpace.coerceAtLeast(0f)

                        anchoredDraggableState.updateAnchors(
                            newAnchors = ContinuousDraggableAnchors(
                                minAnchoredDraggablePosition = minAnchoredDraggablePosition,
                                maxAnchoredDraggablePosition = maxAnchoredDraggablePosition,
                            ).asFoundationDraggableAnchors(
                                equalsKey = minAnchoredDraggablePosition to maxAnchoredDraggablePosition,
                            ),
                            newTarget = anchoredDraggableState.targetValue,
                        )

                        val currentFraction = checkNotNull(
                            anchoredDraggableState.anchors.closestAnchor(
                                anchoredDraggableState.requireOffset(),
                            ),
                        )

                        val listPaneExtraSpace = freeSpace * currentFraction
                        val listPaneWidth =
                            (startInsetsPlaceable.width + minPaneWidthPx + listPaneExtraSpace).roundToInt()
                        val detailPaneWidth = constraints.maxWidth - listPaneWidth

                        val listPanePlaceable = measurables
                            .getValue(ListAndDetailLayoutTypes.List)
                            .measure(constraints.copy(minWidth = listPaneWidth, maxWidth = listPaneWidth))

                        val detailPanePlaceable = measurables
                            .getValue(ListAndDetailLayoutTypes.Detail)
                            .measure(constraints.copy(minWidth = detailPaneWidth, maxWidth = detailPaneWidth))

                        listPanePlaceable.placeRelative(0, 0)
                        detailPanePlaceable.placeRelative(listPaneWidth, 0)

                        val dividerPlaceable = measurables
                            .getValue(ListAndDetailLayoutTypes.Divider)
                            .measure(constraints)

                        dividerPlaceable.placeRelative(listPaneWidth - dividerPlaceable.width / 2, 0)
                    }
                },
            )
        } else {
            AnimatedContent(
                targetState = when (val predictiveBackState = predictiveBackStateHolder.value) {
                    RepeatablePredictiveBackState.NotRunning -> TargetState.Single(showList)
                    is RepeatablePredictiveBackState.Running ->
                        TargetState.InProgress(
                            current = false,
                            provisional = true,
                            progress = predictiveBackState.progress,
                            metadata = predictiveBackState,
                        )
                }.also { println("vanyo: target state for list: $it") },
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
                            is ContentStatus.Disappearing -> {
                                if (contentStatusTargetState.progressToNotVisible >= 0.01f) {
                                    // Only save that we were disappearing if the progress is at least 1% along
                                    value = contentStatusTargetState
                                }
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
                                ) * when (metadata.swipeEdge) {
                                    SwipeEdge.Left -> -1f
                                    SwipeEdge.Right -> 1f
                                }
                            }
                            ContentStatus.NotVisible -> {
                                8.dp * when (lastDisappearingValue?.metadata?.swipeEdge) {
                                    null -> 0f
                                    SwipeEdge.Left -> -1f
                                    SwipeEdge.Right -> 1f
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
                                when (it.metadata.swipeEdge) {
                                    SwipeEdge.Left -> 1f
                                    SwipeEdge.Right -> 0f
                                }
                            }
                            ContentStatus.NotVisible -> {
                                when (lastDisappearingValue?.metadata?.swipeEdge) {
                                    null -> 0.5f
                                    SwipeEdge.Left -> 1f
                                    SwipeEdge.Right -> 0f
                                }
                            }
                            ContentStatus.Visible -> 0.5f
                        }
                    }

                    Box(
                        modifier = Modifier
                            .graphicsLayer {
                                shadowElevation = 6.dp.toPx()
                                this.translationX = translationX.toPx()
                                this.alpha = alpha
                                this.scaleX = scale
                                this.scaleY = scale
                                this.transformOrigin = TransformOrigin(pivotFractionX, 0.5f)
                                shape = RoundedCornerShape(cornerRadius)
                                clip = true
                            },
                        propagateMinConstraints = true,
                    ) {
                        contentWithStatus()
                    }
                },
            ) { targetShowList ->
                if (targetShowList) {
                    Surface {
                        listContent()
                    }
                } else {
                    Surface {
                        detailContent()
                    }
                }
            }
        }
    }
}

data class ContinuousDraggableAnchors(
    private val minAnchoredDraggablePosition: Float,
    private val maxAnchoredDraggablePosition: Float,
) : DraggableAnchors<Float> {

    override val size: Int = 1

    override fun closestAnchor(position: Float): Float =
        (
            position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                minAnchoredDraggablePosition
            ) /
            (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)

    override fun closestAnchor(position: Float, searchUpwards: Boolean): Float? =
        if (searchUpwards) {
            if (position <= maxAnchoredDraggablePosition) {
                (
                    position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                        minAnchoredDraggablePosition
                    ) /
                    (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)
            } else {
                null
            }
        } else {
            if (position >= minAnchoredDraggablePosition) {
                (
                    position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                        minAnchoredDraggablePosition
                    ) /
                    (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)
            } else {
                null
            }
        }

    override fun maxAnchor(): Float = maxAnchoredDraggablePosition

    override fun minAnchor(): Float = minAnchoredDraggablePosition

    override fun positionOf(value: Float): Float =
        value * (maxAnchoredDraggablePosition - minAnchoredDraggablePosition) +
            minAnchoredDraggablePosition

    override fun hasAnchorFor(value: Float): Boolean =
        value in minAnchoredDraggablePosition..maxAnchoredDraggablePosition

    override fun forEach(block: (anchor: Float, position: Float) -> Unit) = Unit
}

sealed interface ListAndDetailLayoutTypes {
    data object StartInsets : ListAndDetailLayoutTypes
    data object EndInsets : ListAndDetailLayoutTypes
    data object List : ListAndDetailLayoutTypes
    data object Detail : ListAndDetailLayoutTypes
    data object Divider : ListAndDetailLayoutTypes

    @GenSealedEnum
    companion object
}

expect val ListAndDetailLayoutTypes.Companion._sealedEnum: SealedEnum<ListAndDetailLayoutTypes>

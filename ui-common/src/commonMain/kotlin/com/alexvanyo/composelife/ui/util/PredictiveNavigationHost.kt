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

import androidx.compose.animation.animateColorAsState
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.Spring
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
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
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
import androidx.compose.runtime.State
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
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
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.lerp
import androidx.compose.ui.util.lerp
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationDecoration
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.previousEntry
import com.livefront.sealedenum.GenSealedEnum
import java.util.UUID
import kotlin.math.roundToInt

@Composable
@Suppress("LongParameterList")
fun <T> PredictiveNavigationHost(
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    backstackState: BackstackState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
    content: @Composable (BackstackEntry<T>) -> Unit,
) = PredictiveNavigationHost(
    backstackState = backstackState,
    modifier = modifier,
    decoration = materialPredictiveNavigationDecoration(
        repeatablePredictiveBackState = repeatablePredictiveBackState,
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
    ),
    content = content,
)

@Composable
@Suppress("LongParameterList")
fun <T> PredictiveNavigationHost(
    backstackState: BackstackState<T>,
    modifier: Modifier = Modifier,
    decoration: NavigationDecoration<BackstackEntry<T>, BackstackState<T>>,
    content: @Composable (BackstackEntry<T>) -> Unit,
) = NavigationHost(
    navigationState = backstackState,
    modifier = modifier,
    decoration = decoration,
    content = content,
)

fun <T> segmentingNavigationDecoration(
    navigationDecoration: NavigationDecoration<
        BackstackEntry<List<BackstackEntry<T>>>,
        BackstackState<List<BackstackEntry<T>>>,
    >,
): NavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { pane ->
    val transformedPane: @Composable (BackstackEntry<List<BackstackEntry<T>>>) -> Unit = { entry ->
        key(entry.id) {
            key(entry.value.first().id) {
                pane(entry.value.first())
            }
        }
    }
    val transformedKeys = entryMap.keys.associateWith {
        key(it) {
            remember { UUID.randomUUID() }
        }
    }
    val transformedEntryMap = remember(transformedKeys) {
        val map = mutableStateMapOf<UUID, BackstackEntry<List<BackstackEntry<T>>>>()
        fun createTransformedEntry(entry: BackstackEntry<T>): BackstackEntry<List<BackstackEntry<T>>> {
            val transformedKey = transformedKeys.getValue(entry.id)
            return map.getOrPut(transformedKey) {
                val transformedPreviousEntry = entry.previous?.let(::createTransformedEntry)

                BackstackEntry(listOf(entry), transformedPreviousEntry, transformedKey)
            }
        }

        entryMap.forEach {
            createTransformedEntry(it.value)
        }
        map
    }

    val currentEntryId = transformedKeys.getValue(currentEntryId)

    val transformedBackstackState: BackstackState<List<BackstackEntry<T>>> =
        object : BackstackState<List<BackstackEntry<T>>> {
            override val entryMap: BackstackMap<List<BackstackEntry<T>>>
                get() = transformedEntryMap
            override val currentEntryId: UUID
                get() = currentEntryId

        }

    navigationDecoration.invoke(transformedBackstackState, transformedPane)
}

fun <T> listDetailNavigationDecoration(
    navigationDecoration: NavigationDecoration<BackstackEntry<T>, BackstackState<T>>,
    onBackButtonPressed: () -> Unit,
): NavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { pane ->
    val currentPane by rememberUpdatedState(pane)

    val idsTransform = entryMap
        .filterValues { it.value !is ListMarker }
        .mapValues { (_, entry) ->
            when (entry.value) {
                is DetailMarker -> entry.previous!!.id
                else -> entry.id
            }
        }

    val transformedPaneMap: Map<UUID, State<@Composable (BackstackEntry<T>) -> Unit>> = entryMap
        .filterValues { it.value !is ListMarker }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailMarker) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (id, entry) ->
            key(id) {
                rememberUpdatedState(
                    when (entry.value) {
                        is DetailMarker -> {
                            {
                                val previous = entry.previous
                                requireNotNull(previous)
                                val listMarker = previous.value as ListMarker
                                val detailMarker = entry.value as DetailMarker

                                ListDetailPane(
                                    showList = listMarker.isListVisible,
                                    showDetail = detailMarker.isDetailVisible,
                                    listContent = {
                                        currentPane(previous)
                                    },
                                    detailContent = {
                                        currentPane(entry)
                                    },
                                    onBackButtonPressed = onBackButtonPressed,
                                )
                            }
                        }

                        else -> {
                            {
                                currentPane(entry)
                            }
                        }
                    }
                )
            }
        }

    val transformedPane: @Composable (BackstackEntry<T>) -> Unit = { entry ->
        key(entry.id) {
            val transformedPane by remember { transformedPaneMap.getValue(entry.id) }
            transformedPane.invoke(entry)
        }
    }

    val transformedEntryMap = entryMap
        .filterValues { it.value !is ListMarker }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailMarker) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (_, entry) ->
            if (entry.value is DetailMarker) {
                BackstackEntry(
                    entry.value,
                    previous = entry.previous!!.previous,
                    id = entry.previous!!.id
                )
            } else {
                entry
            }
        }
    val transformedCurrentEntryId = idsTransform.getValue(currentEntryId)

    val transformedBackstackState: BackstackState<T> =
        object : BackstackState<T> {
            override val entryMap: BackstackMap<T>
                get() = transformedEntryMap
            override val currentEntryId: UUID
                get() = transformedCurrentEntryId

        }

    navigationDecoration.invoke(transformedBackstackState, transformedPane)
}

interface ListMarker : ListDetailInfo

interface DetailMarker : ListDetailInfo

interface ListDetailInfo {
    val isListVisible: Boolean
    val isDetailVisible: Boolean
}

@OptIn(ExperimentalFoundationApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun ListDetailPane(
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

    Surface {
        if (showListAndDetail) {
            Layout(
                layoutIdTypes = ListAndDetailLayoutTypes.sealedEnum,
                modifier = modifier,
                content = {
                    Spacer(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.StartInsets)
                            .windowInsetsStartWidth(androidx.compose.foundation.layout.WindowInsets.safeDrawing),
                    )
                    Spacer(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.EndInsets)
                            .windowInsetsEndWidth(androidx.compose.foundation.layout.WindowInsets.safeDrawing),
                    )

                    Box(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.List)
                            .consumeWindowInsets(
                                androidx.compose.foundation.layout.WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.End
                                )
                            ),
                    ) {
                        listContent()
                    }

                    Column(
                        Modifier
                            .layoutId(ListAndDetailLayoutTypes.Detail)
                            .consumeWindowInsets(
                                androidx.compose.foundation.layout.WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Start
                                )
                            )
                            .windowInsetsPadding(
                                androidx.compose.foundation.layout.WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Horizontal
                                )
                            )
                            .padding(
                                top = 4.dp,
                                start = 8.dp,
                                end = 8.dp,
                                bottom = 16.dp,
                            ),
                    ) {
                        Spacer(Modifier.windowInsetsTopHeight(androidx.compose.foundation.layout.WindowInsets.safeDrawing))
                        Surface(
                            color = MaterialTheme.colorScheme.secondaryContainer,
                            shape = RoundedCornerShape(16.dp),
                            modifier = Modifier
                                .weight(1f)
                                .consumeWindowInsets(
                                    androidx.compose.foundation.layout.WindowInsets.safeDrawing.only(
                                        WindowInsetsSides.Vertical
                                    )
                                ),
                        ) {
                            detailContent()
                        }
                        Spacer(Modifier.windowInsetsBottomHeight(androidx.compose.foundation.layout.WindowInsets.safeDrawing))
                    }

                    Box(
                        modifier = Modifier
                            .layoutId(ListAndDetailLayoutTypes.Divider)
                            .fillMaxHeight()
                            .windowInsetsPadding(
                                androidx.compose.foundation.layout.WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Vertical
                                )
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
                        )
                },
                modifier = modifier,
            ) { targetShowList ->
                if (targetShowList) {
                    listContent()
                } else {
                    detailContent()
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


fun <T> crossfadePredictiveNavigationDecoration(
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
): NavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { pane ->
    val currentPane by rememberUpdatedState(pane)
    val movablePanes = entryMap.mapValues { (id, entry) ->
        key(id) {
            val currentEntry by rememberUpdatedState(entry)
            remember {
                movableContentOf {
                    currentPane(currentEntry)
                }
            }
        }
    }

    val targetState = when (repeatablePredictiveBackState) {
        RepeatablePredictiveBackState.NotRunning -> TargetState.Single(currentEntry)
        is RepeatablePredictiveBackState.Running -> {
            val previous = previousEntry
            if (previous != null) {
                TargetState.InProgress(
                    current = currentEntry,
                    provisional = previous,
                    progress = repeatablePredictiveBackState.progress,
                )
            } else {
                TargetState.Single(currentEntry)
            }
        }
    }

    AnimatedContent(
        targetState = targetState,
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
    ) { entry ->
        key(entry.id) {
            // Fetch and store the movable content to hold onto while animating out
            val movablePane = remember { movablePanes.getValue(entry.id) }
            movablePane()
        }
    }
}

/**
 * A [NavigationDecoration] that implements the Material predictive back design for animating between panes upon
 * popping.
 *
 * https://developer.android.com/design/ui/mobile/guides/patterns/predictive-back#full-pane-surfaces
 */
@Suppress("CyclomaticComplexMethod", "LongMethod")
fun <T> materialPredictiveNavigationDecoration(
    repeatablePredictiveBackState: RepeatablePredictiveBackState,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
): NavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { pane ->
    val currentPane by rememberUpdatedState(pane)
    val movablePanes = entryMap.mapValues { (id, entry) ->
        key(id) {
            val currentEntry by rememberUpdatedState(entry)
            remember {
                movableContentOf {
                    currentPane(currentEntry)
                }
            }
        }
    }

    val targetState = when (repeatablePredictiveBackState) {
        RepeatablePredictiveBackState.NotRunning -> TargetState.Single(currentEntry)
        is RepeatablePredictiveBackState.Running -> {
            val previous = previousEntry
            if (previous != null) {
                TargetState.InProgress(
                    current = currentEntry,
                    provisional = previous,
                    progress = repeatablePredictiveBackState.progress,
                    metadata = repeatablePredictiveBackState,
                )
            } else {
                TargetState.Single(currentEntry)
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
        targetRenderingComparator = compareByDescending { entry ->
            // Render items in order of the backstack, with the top of the backstack rendered last
            // If the entry is not in the backstack at all, assume that it is disappearing aftering being popped, and
            // render it on top of everything still in the backstack
            generateSequence(
                currentEntry,
                BackstackEntry<T>::previous,
            ).indexOfFirst { it.id == entry.id }
        },
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        contentKey = BackstackEntry<T>::id,
    ) { entry ->
        key(entry.id) {
            // Fetch and store the movable content to hold onto while animating out
            val movablePane = remember { movablePanes.getValue(entry.id) }
            movablePane()
        }
    }
}

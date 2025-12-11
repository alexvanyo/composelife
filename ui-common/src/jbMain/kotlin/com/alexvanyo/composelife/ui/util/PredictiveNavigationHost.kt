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
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.mutableStateSetOf
import androidx.compose.runtime.remember
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
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.scene.OverlayScene
import androidx.navigation3.scene.Scene
import androidx.navigationevent.NavigationEvent
import androidx.navigationevent.NavigationEventTransitionState
import com.alexvanyo.composelife.navigation3.scene.LocalEntriesToExcludeFromCurrentScene
import com.alexvanyo.composelife.navigation3.scene.SceneState
import kotlin.reflect.KClass

@Suppress("LongParameterList", "LongMethod")
@Composable
fun <T : Any> CrossfadePredictiveNavDisplay(
    sceneState: SceneState<T>,
    navigationEventTransitionState: NavigationEventTransitionState,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
) {
    val navDisplayState = rememberNavDisplayState(
        sceneState = sceneState,
        navigationEventTransitionState = navigationEventTransitionState,
    )

    Box(modifier = modifier) {
        AnimatedContent(
            animatedContentState = navDisplayState.animatedContentState,
            contentAlignment = contentAlignment,
            contentSizeAnimationSpec = contentSizeAnimationSpec,
            animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        ) { targetScene ->
            CompositionLocalProvider(
                LocalEntriesToExcludeFromCurrentScene provides
                    navDisplayState.entriesToExcludeFromCurrentScene.getValue(targetScene::class to targetScene.key),
            ) {
                targetScene.content()
            }
        }

        AnimatedContent(
            animatedContentState = navDisplayState.overlayAnimatedContentState,
            contentAlignment = contentAlignment,
            contentSizeAnimationSpec = contentSizeAnimationSpec,
            animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        ) { targetOverlayScene ->
            if (targetOverlayScene != null) {
                CompositionLocalProvider(
                    LocalEntriesToExcludeFromCurrentScene provides
                        navDisplayState.entriesToExcludeFromCurrentScene.getValue(
                            targetOverlayScene::class to targetOverlayScene.key,
                        ),
                ) {
                    targetOverlayScene.content()
                }
            }
        }
    }
}

interface NavDisplayState<T : Any> {
    val animatedContentState:
        AnimatedContentState<Scene<T>, NavigationEventTransitionState.InProgress, Pair<KClass<out Scene<T>>, Any>>

    val overlayAnimatedContentState:
        AnimatedContentState<
            OverlayScene<T>?,
            NavigationEventTransitionState.InProgress,
            Pair<KClass<out OverlayScene<T>>, Any>?,
            >

    val entriesToExcludeFromCurrentScene: Map<Pair<KClass<out Scene<T>>, Any>, Set<Any>>
}

@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun <T : Any> rememberNavDisplayState(
    sceneState: SceneState<T>,
    navigationEventTransitionState: NavigationEventTransitionState,
): NavDisplayState<T> {
    val targetState = when (navigationEventTransitionState) {
        NavigationEventTransitionState.Idle -> TargetState.Single(sceneState.currentScene)
        is NavigationEventTransitionState.InProgress -> {
            val previous = sceneState.previousScenes.lastOrNull()
            if (previous != null) {
                TargetState.InProgress(
                    current = sceneState.currentScene,
                    provisional = previous,
                    progress = navigationEventTransitionState.latestEvent.progress,
                    metadata = navigationEventTransitionState,
                )
            } else {
                TargetState.Single(sceneState.currentScene)
            }
        }
    }
    val overlayTargetState = when (navigationEventTransitionState) {
        NavigationEventTransitionState.Idle -> TargetState.Single(sceneState.overlayScenes.lastOrNull())
        is NavigationEventTransitionState.InProgress -> {
            val previous = sceneState.overlayScenes.getOrNull(sceneState.overlayScenes.lastIndex - 1)
            if (previous != null) {
                TargetState.InProgress(
                    current = sceneState.overlayScenes.lastOrNull(),
                    provisional = previous,
                    progress = navigationEventTransitionState.latestEvent.progress,
                    metadata = navigationEventTransitionState,
                )
            } else {
                TargetState.Single(sceneState.overlayScenes.lastOrNull())
            }
        }
    }

    val animatedContentState = rememberAnimatedContentState(
        targetState = targetState,
        contentKey = { it::class to it.key },
        label = "rememberNavDisplayStateTargetState",
    )
    val overlayAnimatedContentState = rememberAnimatedContentState(
        targetState = overlayTargetState,
        contentKey = { it?.let { it::class to it.key } },
        label = "rememberNavDisplayStateOverlayTargetState",
    )

    val previousMostRecentTargetSceneKeys = remember {
        mutableStateSetOf<Pair<KClass<out Scene<T>>, Any>>()
    }
    val newMostRecentTargetSceneKeys =
        when (targetState) {
            is TargetState.InProgress<Scene<T>, *> -> {
                listOf(
                    targetState.current::class to targetState.current.key,
                    targetState.provisional::class to targetState.provisional.key,
                )
            }
            is TargetState.Single<Scene<T>> -> {
                listOf(
                    targetState.current::class to targetState.current.key,
                )
            }
        } + when (overlayTargetState) {
            is TargetState.InProgress<OverlayScene<T>?, *> -> {
                val current = overlayTargetState.current
                val provisional = overlayTargetState.provisional
                listOfNotNull(
                    current?.let { it::class to it.key },
                    provisional?.let { it::class to it.key },
                )
            }
            is TargetState.Single<OverlayScene<T>?> -> {
                val current = overlayTargetState.current
                listOfNotNull(
                    current?.let { it::class to it.key },
                )
            }
        }
    val currentMostRecentTargetScenes = previousMostRecentTargetSceneKeys
        .toMutableSet()
        .apply {
            removeAll(newMostRecentTargetSceneKeys)
            addAll(newMostRecentTargetSceneKeys)
        }
    val scenesInTransition = remember {
        mutableStateMapOf<Pair<KClass<out Scene<T>>, Any>, Scene<T>>()
    }

    DisposableEffect(
        previousMostRecentTargetSceneKeys.toList(),
        currentMostRecentTargetScenes.toList(),
    ) {
        if (currentMostRecentTargetScenes.toList() != previousMostRecentTargetSceneKeys.toList()) {
            previousMostRecentTargetSceneKeys.clear()
            previousMostRecentTargetSceneKeys.addAll(currentMostRecentTargetScenes)
        }
        onDispose {}
    }
    val currentTargetKeysInTransition = animatedContentState.currentTargetsInTransition.keys.toSet() +
        overlayAnimatedContentState.currentTargetsInTransition.keys.toSet()
    DisposableEffect(
        currentTargetKeysInTransition,
    ) {
        previousMostRecentTargetSceneKeys.removeAll { it !in currentTargetKeysInTransition }
        scenesInTransition.keys.toList().forEach { key ->
            if (key !in currentTargetKeysInTransition) {
                scenesInTransition.remove(key)
            }
        }
        onDispose {}
    }

    val currentScenesByKey = (sceneState.overlayScenes + listOf(sceneState.currentScene) + sceneState.previousScenes)
        .associateBy { it::class to it.key }

    scenesInTransition.putAll(currentScenesByKey)

    val entriesBySceneKey = scenesInTransition.mapValues { (_, scene) -> scene.entries }
    val entryKeysBySceneKey = entriesBySceneKey.mapValues { (_, entries) -> entries.map(NavEntry<T>::contentKey) }

    val entriesToExcludeFromCurrentScene = remember(
        currentMostRecentTargetScenes.toList(),
        entryKeysBySceneKey,
    ) {
        buildMap {
            val coveredEntryKeys = mutableSetOf<Any>()
            currentMostRecentTargetScenes.reversed().forEach { sceneKey ->
                put(sceneKey, coveredEntryKeys.toSet())
                coveredEntryKeys.addAll(entryKeysBySceneKey.getValue(sceneKey))
            }
        }
    }

    return object : NavDisplayState<T> {
        override val animatedContentState:
            AnimatedContentState<Scene<T>, NavigationEventTransitionState.InProgress, Pair<KClass<out Scene<T>>, Any>>
            get() = animatedContentState

        override val overlayAnimatedContentState:
            AnimatedContentState<
                OverlayScene<T>?,
                NavigationEventTransitionState.InProgress,
                Pair<KClass<out OverlayScene<T>>, Any>?,
                >
            get() = overlayAnimatedContentState

        override val entriesToExcludeFromCurrentScene: Map<Pair<KClass<out Scene<T>>, Any>, Set<Any>>
            get() = entriesToExcludeFromCurrentScene
    }
}

@Suppress("CyclomaticComplexMethod", "LongMethod", "LongParameterList")
@Composable
fun <T : Any> MaterialPredictiveNavDisplay(
    sceneState: SceneState<T>,
    navigationEventTransitionState: NavigationEventTransitionState,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    animateInternalContentSizeChanges: Boolean = false,
    clipUsingWindowShape: Boolean = false,
) {
    val navDisplayState = rememberNavDisplayState(
        sceneState = sceneState,
        navigationEventTransitionState = navigationEventTransitionState,
    )

    Box(modifier = modifier) {
        AnimatedContent(
            animatedContentState = navDisplayState.animatedContentState,
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
                    mutableStateOf<ContentStatus.Disappearing<out NavigationEventTransitionState.InProgress>?>(
                        null,
                    )
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
                            ) * when (metadata.latestEvent.swipeEdge) {
                                NavigationEvent.EDGE_LEFT -> -1f
                                NavigationEvent.EDGE_RIGHT -> 1f
                                else -> 0f
                            }
                        }
                        ContentStatus.NotVisible -> {
                            8.dp * when (lastDisappearingValue?.metadata?.latestEvent?.swipeEdge) {
                                NavigationEvent.EDGE_LEFT -> -1f
                                NavigationEvent.EDGE_RIGHT -> 1f
                                else -> 0f
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
                            when (it.metadata.latestEvent.swipeEdge) {
                                NavigationEvent.EDGE_LEFT -> 1f
                                NavigationEvent.EDGE_RIGHT -> 0f
                                else -> 0.5f
                            }
                        }
                        ContentStatus.NotVisible -> {
                            when (lastDisappearingValue?.metadata?.latestEvent?.swipeEdge) {
                                NavigationEvent.EDGE_LEFT -> 1f
                                NavigationEvent.EDGE_RIGHT -> 0f
                                else -> 0.5f
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
                                        RoundRect(size.toRect(), CornerRadius(cornerRadius.toPx())),
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
            targetRenderingComparator = compareByDescending { scene ->
                // Render items in order of the backstack, with the top of the backstack rendered last
                // If the entry is not in the backstack at all, assume that it is disappearing after being popped, and
                // render it on top of everything still in the backstack
                (listOf(sceneState.currentScene) + sceneState.previousScenes.reversed())
                    .indexOfLast { it::class to it.key == scene::class to scene.key }
            },
            contentSizeAnimationSpec = contentSizeAnimationSpec,
            animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        ) { targetScene ->
            CompositionLocalProvider(
                LocalEntriesToExcludeFromCurrentScene provides
                    navDisplayState.entriesToExcludeFromCurrentScene.getValue(targetScene::class to targetScene.key),
            ) {
                targetScene.content()
            }
        }

        AnimatedContent(
            animatedContentState = navDisplayState.overlayAnimatedContentState,
            contentAlignment = contentAlignment,
            targetRenderingComparator = compareByDescending { scene ->
                // Render items in order of the backstack, with the top of the backstack rendered last
                // If the entry is not in the backstack at all, assume that it is disappearing after being popped, and
                // render it on top of everything still in the backstack
                (sceneState.overlayScenes.reversed())
                    .indexOfLast { it::class to it.key == scene?.let { it::class to it.key } }
            },
            contentSizeAnimationSpec = contentSizeAnimationSpec,
            animateInternalContentSizeChanges = animateInternalContentSizeChanges,
        ) { targetOverlayScene ->
            if (targetOverlayScene != null) {
                CompositionLocalProvider(
                    LocalEntriesToExcludeFromCurrentScene provides
                        navDisplayState.entriesToExcludeFromCurrentScene.getValue(
                            targetOverlayScene::class to targetOverlayScene.key,
                        ),
                ) {
                    targetOverlayScene.content()
                }
            }
        }
    }
}

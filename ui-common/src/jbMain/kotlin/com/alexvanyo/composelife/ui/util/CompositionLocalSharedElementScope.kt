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

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.AnimatedVisibilityScope
import androidx.compose.animation.BoundsTransform
import androidx.compose.animation.EnterTransition
import androidx.compose.animation.ExitTransition
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionScope
import androidx.compose.animation.SharedTransitionScope.OverlayClip
import androidx.compose.animation.SharedTransitionScope.PlaceHolderSize
import androidx.compose.animation.SharedTransitionScope.PlaceHolderSize.Companion.contentSize
import androidx.compose.animation.SharedTransitionScope.ResizeMode
import androidx.compose.animation.SharedTransitionScope.ResizeMode.Companion.ScaleToBounds
import androidx.compose.animation.SharedTransitionScope.SharedContentState
import androidx.compose.animation.core.Spring.StiffnessMediumLow
import androidx.compose.animation.core.VisibilityThreshold
import androidx.compose.animation.core.spring
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.compositionLocalOf
import androidx.compose.ui.Alignment.Companion.Center
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection

@Suppress("ComposeCompositionLocalUsage")
val LocalNavigationAnimatedVisibilityScope: ProvidableCompositionLocal<AnimatedVisibilityScope?> =
    compositionLocalOf { null }

@OptIn(ExperimentalSharedTransitionApi::class)
@Suppress("ComposeCompositionLocalUsage")
val LocalNavigationSharedTransitionScope: ProvidableCompositionLocal<SharedTransitionScope?> =
    compositionLocalOf { null }

@Suppress("ComposeComposableModifier", "ComposeModifierWithoutDefault", "LongParameterList")
@OptIn(ExperimentalSharedTransitionApi::class)
@Composable
fun Modifier.trySharedElement(
    key: Any,
    boundsTransform: BoundsTransform = DefaultBoundsTransform,
    placeHolderSize: PlaceHolderSize = contentSize,
    renderInOverlayDuringTransition: Boolean = true,
    zIndexInOverlay: Float = 0f,
    clipInOverlayDuringTransition: OverlayClip = ParentClip,
): Modifier {
    val animatedVisibilityScope = LocalNavigationAnimatedVisibilityScope.current
    val sharedTransitionScope = LocalNavigationSharedTransitionScope.current

    return this.then(
        if (animatedVisibilityScope == null || sharedTransitionScope == null) {
            Modifier
        } else {
            with(sharedTransitionScope) {
                Modifier.sharedElement(
                    sharedContentState = rememberSharedContentState(key),
                    animatedVisibilityScope = animatedVisibilityScope,
                    boundsTransform = boundsTransform,
                    placeHolderSize = placeHolderSize,
                    renderInOverlayDuringTransition = renderInOverlayDuringTransition,
                    zIndexInOverlay = zIndexInOverlay,
                    clipInOverlayDuringTransition = clipInOverlayDuringTransition,
                )
            }
        },
    )
}

@Suppress("ComposeComposableModifier", "ComposeModifierWithoutDefault", "LongParameterList")
@OptIn(ExperimentalSharedTransitionApi::class)
@Composable
fun Modifier.trySharedBounds(
    key: Any,
    enter: EnterTransition = fadeIn(),
    exit: ExitTransition = fadeOut(),
    boundsTransform: BoundsTransform = DefaultBoundsTransform,
    resizeMode: ResizeMode = ScaleToBounds(ContentScale.FillWidth, Center),
    placeHolderSize: PlaceHolderSize = contentSize,
    renderInOverlayDuringTransition: Boolean = true,
    zIndexInOverlay: Float = 0f,
    clipInOverlayDuringTransition: OverlayClip = ParentClip,
): Modifier {
    val animatedVisibilityScope = LocalNavigationAnimatedVisibilityScope.current
    val sharedTransitionScope = LocalNavigationSharedTransitionScope.current

    return this.then(
        if (animatedVisibilityScope == null || sharedTransitionScope == null) {
            Modifier
        } else {
            with(sharedTransitionScope) {
                Modifier.sharedBounds(
                    sharedContentState = rememberSharedContentState(key),
                    animatedVisibilityScope = animatedVisibilityScope,
                    enter = enter,
                    exit = exit,
                    boundsTransform = boundsTransform,
                    resizeMode = resizeMode,
                    placeHolderSize = placeHolderSize,
                    renderInOverlayDuringTransition = renderInOverlayDuringTransition,
                    zIndexInOverlay = zIndexInOverlay,
                    clipInOverlayDuringTransition = clipInOverlayDuringTransition,
                )
            }
        },
    )
}

@Suppress("ComposeComposableModifier", "ComposeModifierWithoutDefault", "LongParameterList")
@OptIn(ExperimentalSharedTransitionApi::class)
@Composable
fun Modifier.trySharedElementWithCallerManagedVisibility(
    key: Any,
    visible: Boolean,
    boundsTransform: BoundsTransform = DefaultBoundsTransform,
    placeHolderSize: PlaceHolderSize = contentSize,
    renderInOverlayDuringTransition: Boolean = true,
    zIndexInOverlay: Float = 0f,
    clipInOverlayDuringTransition: OverlayClip = ParentClip,
): Modifier {
    val sharedTransitionScope = LocalNavigationSharedTransitionScope.current

    return this.then(
        if (sharedTransitionScope == null) {
            Modifier
        } else {
            with(sharedTransitionScope) {
                Modifier.sharedElementWithCallerManagedVisibility(
                    sharedContentState = rememberSharedContentState(key),
                    visible = visible,
                    boundsTransform = boundsTransform,
                    placeHolderSize = placeHolderSize,
                    renderInOverlayDuringTransition = renderInOverlayDuringTransition,
                    zIndexInOverlay = zIndexInOverlay,
                    clipInOverlayDuringTransition = clipInOverlayDuringTransition,
                )
            }
        },
    )
}

// Defaults copied from SharedTransitionScope.kt

@ExperimentalSharedTransitionApi
internal val DefaultBoundsTransform = BoundsTransform { _, _ ->
    spring(
        stiffness = StiffnessMediumLow,
        visibilityThreshold = Rect.VisibilityThreshold,
    )
}

@ExperimentalSharedTransitionApi
internal val ParentClip: OverlayClip =
    object : OverlayClip {
        override fun getClipPath(
            sharedContentState: SharedContentState,
            bounds: Rect,
            layoutDirection: LayoutDirection,
            density: Density,
        ): Path? {
            return sharedContentState.parentSharedContentState?.clipPathInOverlay
        }
    }

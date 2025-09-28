/*
 * Copyright 2025 The Android Open Source Project
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
import androidx.compose.ui.Modifier

@OptIn(ExperimentalSharedTransitionApi::class)
context(sharedTransitionScope: SharedTransitionScope)
@Suppress("LongParameterList")
internal actual fun Modifier.sharedElement(
    sharedContentState: SharedTransitionScope.SharedContentState,
    animatedVisibilityScope: AnimatedVisibilityScope,
    boundsTransform: BoundsTransform,
    placeholderSize: PlaceholderSize,
    renderInOverlayDuringTransition: Boolean,
    zIndexInOverlay: Float,
    clipInOverlayDuringTransition: SharedTransitionScope.OverlayClip,
): Modifier = with(sharedTransitionScope) {
    sharedElement(
        sharedContentState = sharedContentState,
        animatedVisibilityScope = animatedVisibilityScope,
        boundsTransform = boundsTransform,
        placeHolderSize = placeholderSize,
        renderInOverlayDuringTransition = renderInOverlayDuringTransition,
        zIndexInOverlay = zIndexInOverlay,
        clipInOverlayDuringTransition = clipInOverlayDuringTransition,
    )
}

@OptIn(ExperimentalSharedTransitionApi::class)
context(sharedTransitionScope: SharedTransitionScope)
@Suppress("LongParameterList")
internal actual fun Modifier.sharedBounds(
    sharedContentState: SharedTransitionScope.SharedContentState,
    animatedVisibilityScope: AnimatedVisibilityScope,
    enter: EnterTransition,
    exit: ExitTransition,
    boundsTransform: BoundsTransform,
    resizeMode: SharedTransitionScope.ResizeMode,
    placeholderSize: PlaceholderSize,
    renderInOverlayDuringTransition: Boolean,
    zIndexInOverlay: Float,
    clipInOverlayDuringTransition: SharedTransitionScope.OverlayClip,
): Modifier = with(sharedTransitionScope) {
    sharedBounds(
        sharedContentState = sharedContentState,
        animatedVisibilityScope = animatedVisibilityScope,
        enter = enter,
        exit = exit,
        boundsTransform = boundsTransform,
        resizeMode = resizeMode,
        placeHolderSize = placeholderSize,
        renderInOverlayDuringTransition = renderInOverlayDuringTransition,
        zIndexInOverlay = zIndexInOverlay,
        clipInOverlayDuringTransition = clipInOverlayDuringTransition,
    )
}

@OptIn(ExperimentalSharedTransitionApi::class)
context(sharedTransitionScope: SharedTransitionScope)
@Suppress("LongParameterList")
internal actual fun Modifier.sharedElementWithCallerManagedVisibility(
    sharedContentState: SharedTransitionScope.SharedContentState,
    visible: Boolean,
    boundsTransform: BoundsTransform,
    placeholderSize: PlaceholderSize,
    renderInOverlayDuringTransition: Boolean,
    zIndexInOverlay: Float,
    clipInOverlayDuringTransition: SharedTransitionScope.OverlayClip,
): Modifier = with(sharedTransitionScope) {
    sharedElementWithCallerManagedVisibility(
        sharedContentState = sharedContentState,
        visible = visible,
        boundsTransform = boundsTransform,
        placeHolderSize = placeholderSize,
        renderInOverlayDuringTransition = renderInOverlayDuringTransition,
        zIndexInOverlay = zIndexInOverlay,
        clipInOverlayDuringTransition = clipInOverlayDuringTransition,
    )
}

@OptIn(ExperimentalSharedTransitionApi::class)
actual typealias PlaceholderSize = SharedTransitionScope.PlaceHolderSize

@OptIn(ExperimentalSharedTransitionApi::class)
actual val ContentSize: PlaceholderSize = SharedTransitionScope.PlaceHolderSize.contentSize

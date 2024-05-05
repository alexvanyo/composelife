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
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.layout.LookaheadScope

@OptIn(ExperimentalSharedTransitionApi::class)
@Composable
actual fun SharedTransitionScope(
    content: @Composable SharedTransitionScope.(Modifier) -> Unit,
) = androidx.compose.animation.SharedTransitionScope { modifier ->
    val scopeImpl = remember(this) {
        SharedTransitionScopeImpl(this)
    }
    content.invoke(scopeImpl, modifier)
}

@OptIn(ExperimentalSharedTransitionApi::class)
private class SharedTransitionScopeImpl(
    private val actualSharedTransitionScope: androidx.compose.animation.SharedTransitionScope,
) : SharedTransitionScope, LookaheadScope by actualSharedTransitionScope {
    override fun Modifier.sharedElementWithCallerManagedVisibility(
        sharedContentState: SharedTransitionScope.SharedContentState,
        visible: Boolean,
        renderInOverlayDuringTransition: Boolean,
        zIndexInOverlay: Float,
    ): Modifier = with(actualSharedTransitionScope) {
        sharedElementWithCallerManagedVisibility(
            sharedContentState = (sharedContentState as SharedContentState).actualSharedContentState,
            visible = visible,
            renderInOverlayDuringTransition = renderInOverlayDuringTransition,
            zIndexInOverlay = zIndexInOverlay,
        )
    }

    override fun Modifier.sharedElement(
        sharedContentState: SharedTransitionScope.SharedContentState,
        animatedVisibilityScope: AnimatedVisibilityScope,
        renderInOverlayDuringTransition: Boolean,
        zIndexInOverlay: Float,
    ): Modifier = with(actualSharedTransitionScope) {
        sharedElement(
            state = (sharedContentState as SharedContentState).actualSharedContentState,
            animatedVisibilityScope = animatedVisibilityScope,
            renderInOverlayDuringTransition = renderInOverlayDuringTransition,
            zIndexInOverlay = zIndexInOverlay,
        )
    }

    @Suppress("ComposeUnstableReceiver")
    @Composable
    override fun rememberSharedContentState(key: Any): SharedContentState {
        val actualSharedContentState = actualSharedTransitionScope.rememberSharedContentState(key)
        return remember(actualSharedContentState) {
            SharedContentState(actualSharedContentState)
        }
    }

    class SharedContentState(
        val actualSharedContentState: androidx.compose.animation.SharedTransitionScope.SharedContentState,
    ) : SharedTransitionScope.SharedContentState {
        override val isMatchFound: Boolean
            get() = actualSharedContentState.isMatchFound
        override val clipPathInOverlay: Path?
            get() = actualSharedContentState.clipPathInOverlay
        override val parentSharedContentState: SharedTransitionScope.SharedContentState?
            get() = actualSharedContentState.parentSharedContentState?.let(::SharedContentState)
    }
}

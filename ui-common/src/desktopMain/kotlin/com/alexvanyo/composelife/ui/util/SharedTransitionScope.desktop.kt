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
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.layout.LookaheadScope

@Composable
actual fun SharedTransitionScope(
    content: @Composable SharedTransitionScope.(Modifier) -> Unit,
) = LookaheadScope {
    val scopeImpl = remember(this) {
        SharedTransitionScopeImpl(this)
    }
    content.invoke(scopeImpl, Modifier)
}

class SharedTransitionScopeImpl(
    private val lookaheadScope: LookaheadScope,
) : SharedTransitionScope, LookaheadScope by lookaheadScope {
    override fun Modifier.sharedElementWithCallerManagedVisibility(
        sharedContentState: SharedTransitionScope.SharedContentState,
        visible: Boolean,
        renderInOverlayDuringTransition: Boolean,
        zIndexInOverlay: Float,
    ): Modifier = this

    override fun Modifier.sharedElement(
        sharedContentState: SharedTransitionScope.SharedContentState,
        animatedVisibilityScope: AnimatedVisibilityScope,
        renderInOverlayDuringTransition: Boolean,
        zIndexInOverlay: Float,
    ): Modifier = this

    @Composable
    override fun rememberSharedContentState(key: Any): SharedTransitionScope.SharedContentState = SharedContentState

    object SharedContentState : SharedTransitionScope.SharedContentState {
        override val isMatchFound: Boolean = false
        override val clipPathInOverlay: Path? = null
        override val parentSharedContentState: SharedTransitionScope.SharedContentState? = null
    }
}

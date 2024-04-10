/*
 * Copyright 2022 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.platform.InfiniteAnimationPolicy
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import kotlinx.coroutines.awaitCancellation

@Composable
actual fun GameOfLifeProgressIndicatorForegroundEffect(
    temporalGameOfLifeState: TemporalGameOfLifeState,
) {
    val lifecycleOwner = LocalLifecycleOwner.current
    LaunchedEffect(lifecycleOwner, temporalGameOfLifeState) {
        // If we are not visible, don't animate
        lifecycleOwner.repeatOnLifecycle(Lifecycle.State.STARTED) {
            try {
                // If we are in tests, avoid running the infinite animation
                // It's fine if we only check this upon being started
                if (coroutineContext[InfiniteAnimationPolicy] == null) {
                    temporalGameOfLifeState.setIsRunning(true)
                    awaitCancellation()
                }
            } finally {
                temporalGameOfLifeState.setIsRunning(false)
            }
        }
    }
}

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

@file:Suppress("MatchingDeclarationName", "Filename")

package com.alexvanyo.composelife.ui.util

import androidx.activity.BackEventCompat
import androidx.activity.OnBackPressedCallback
import androidx.activity.compose.LocalOnBackPressedDispatcherOwner
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalLifecycleOwner

/**
 * The state describing an in-progress predictive back animation.
 */
sealed interface PredictiveBackState {
    /**
     * There is no predictive back ongoing. On API 33 and below, this will always be the case.
     */
    object NotRunning : PredictiveBackState

    /**
     * There is an ongoing predictive back animation, with the given [progress].
     */
    data class Running(
        val progress: Float,
    ) : PredictiveBackState
}

@Composable
fun predictiveBackHandler(
    enabled: Boolean = true,
    onBack: () -> Unit,
): PredictiveBackState {
    // Safely update the current `onBack` lambda when a new one is provided
    val currentOnBack by rememberUpdatedState(onBack)

    var predictiveBackState: PredictiveBackState by remember {
        mutableStateOf(PredictiveBackState.NotRunning)
    }

    // Remember in Composition a back callback that calls the `onBack` lambda
    val backCallback = remember {
        object : OnBackPressedCallback(enabled) {
            override fun handleOnBackPressed() {
                currentOnBack()
                predictiveBackState = PredictiveBackState.NotRunning
            }

            override fun handleOnBackCancelled() {
                super.handleOnBackCancelled()
                predictiveBackState = PredictiveBackState.NotRunning
            }

            override fun handleOnBackStarted(backEvent: BackEventCompat) {
                super.handleOnBackStarted(backEvent)
                predictiveBackState = PredictiveBackState.Running(backEvent.progress)
            }

            override fun handleOnBackProgressed(backEvent: BackEventCompat) {
                super.handleOnBackProgressed(backEvent)
                predictiveBackState = PredictiveBackState.Running(backEvent.progress)
            }
        }
    }
    // On every successful composition, update the callback with the `enabled` value
    DisposableEffect(enabled) {
        backCallback.isEnabled = enabled
        onDispose {}
    }
    val backDispatcher = checkNotNull(LocalOnBackPressedDispatcherOwner.current) {
        "No OnBackPressedDispatcherOwner was provided via LocalOnBackPressedDispatcherOwner"
    }.onBackPressedDispatcher
    val lifecycleOwner = LocalLifecycleOwner.current
    DisposableEffect(lifecycleOwner, backDispatcher) {
        // Add callback to the backDispatcher
        backDispatcher.addCallback(lifecycleOwner, backCallback)
        // When the effect leaves the Composition, remove the callback
        onDispose {
            backCallback.remove()
        }
    }

    return if (enabled) predictiveBackState else PredictiveBackState.NotRunning
}

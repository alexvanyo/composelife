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
import androidx.activity.compose.PredictiveBackHandler
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.rememberUpdatedState
import kotlinx.coroutines.CancellationException

@Composable
actual fun RepeatablePredictiveBackHandler(
    repeatablePredictiveBackStateHolder: RepeatablePredictiveBackStateHolder,
    enabled: Boolean,
    onBack: () -> Unit,
) {
    // Safely update the current `onBack` lambda when a new one is provided
    val currentOnBack by rememberUpdatedState(onBack)

    key(repeatablePredictiveBackStateHolder) {
        when (repeatablePredictiveBackStateHolder) {
            is RepeatablePredictiveBackStateHolderImpl -> Unit
        }
        PredictiveBackHandler(enabled = enabled) { progress ->
            try {
                progress.collect { backEvent ->
                    backEvent.swipeEdge
                    repeatablePredictiveBackStateHolder.value = RepeatablePredictiveBackState.Running(
                        backEvent.touchX,
                        backEvent.touchY,
                        backEvent.progress,
                        when (backEvent.swipeEdge) {
                            BackEventCompat.EDGE_LEFT -> SwipeEdge.Left
                            BackEventCompat.EDGE_RIGHT -> SwipeEdge.Right
                            else -> error("Unknown swipe edge")
                        },
                    )
                }
                currentOnBack()
            } finally {
                repeatablePredictiveBackStateHolder.value = RepeatablePredictiveBackState.NotRunning
            }
        }
    }
}

@Composable
actual fun CompletablePredictiveBackStateHandler(
    completablePredictiveBackStateHolder: CompletablePredictiveBackStateHolder,
    enabled: Boolean,
    onBack: () -> Unit,
) {
    // Safely update the current `onBack` lambda when a new one is provided
    val currentOnBack by rememberUpdatedState(onBack)

    key(completablePredictiveBackStateHolder) {
        when (completablePredictiveBackStateHolder) {
            is CompletablePredictiveBackStateHolderImpl -> Unit
        }
        PredictiveBackHandler(enabled = enabled) { progress ->
            try {
                progress.collect { backEvent ->
                    backEvent.swipeEdge
                    completablePredictiveBackStateHolder.value = CompletablePredictiveBackState.Running(
                        backEvent.touchX,
                        backEvent.touchY,
                        backEvent.progress,
                        when (backEvent.swipeEdge) {
                            BackEventCompat.EDGE_LEFT -> SwipeEdge.Left
                            BackEventCompat.EDGE_RIGHT -> SwipeEdge.Right
                            else -> error("Unknown swipe edge")
                        },
                    )
                }
                currentOnBack()
                completablePredictiveBackStateHolder.value = CompletablePredictiveBackState.Completed
            } catch (cancellationException: CancellationException) {
                completablePredictiveBackStateHolder.value = CompletablePredictiveBackState.NotRunning
                throw cancellationException
            }
        }
    }
}

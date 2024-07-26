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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue

/**
 * The state describing a repeatable back state, with use in a [RepeatablePredictiveBackHandler].
 *
 * Because the back handler can be used repeatedly, there are only two states that [RepeatablePredictiveBackState] can
 * be in:
 *
 * - [NotRunning], which will always be the case on API 33 and below
 * - [Running], which can happen on API 34 and above if a predictive back is in progress.
 */
sealed interface RepeatablePredictiveBackState {
    /**
     * There is no predictive back ongoing. On API 33 and below, this will always be the case.
     */
    data object NotRunning : RepeatablePredictiveBackState

    /**
     * There is an ongoing predictive back animation, with the given [progress].
     */
    data class Running(
        val touchX: Float,
        val touchY: Float,
        val progress: Float,
        val swipeEdge: SwipeEdge,
    ) : RepeatablePredictiveBackState
}

/**
 * The state describing a one-shot back state, with use in a [CompletablePredictiveBackStateHandler].
 *
 * Because the back handler can only be used once there are three states that [CompletablePredictiveBackState] can
 * be in:
 *
 * - [NotRunning]
 * - [Running], which can happen on API 34 and above if a predictive back is in progress.
 * - [Completed]
 */
sealed interface CompletablePredictiveBackState {
    /**
     * There is no predictive back ongoing, and the back has not been completed.
     */
    data object NotRunning : CompletablePredictiveBackState

    /**
     * There is an ongoing predictive back animation, with the given [progress].
     */
    data class Running(
        val touchX: Float,
        val touchY: Float,
        val progress: Float,
        val swipeEdge: SwipeEdge,
    ) : CompletablePredictiveBackState

    /**
     * The back has completed.
     */
    data object Completed : CompletablePredictiveBackState
}

sealed interface SwipeEdge {
    data object Left : SwipeEdge
    data object Right : SwipeEdge
}

@Composable
fun rememberRepeatablePredictiveBackStateHolder(): RepeatablePredictiveBackStateHolder =
    remember {
        RepeatablePredictiveBackStateHolderImpl()
    }

sealed interface RepeatablePredictiveBackStateHolder {
    val value: RepeatablePredictiveBackState
}

internal class RepeatablePredictiveBackStateHolderImpl : RepeatablePredictiveBackStateHolder {
    override var value: RepeatablePredictiveBackState by mutableStateOf(RepeatablePredictiveBackState.NotRunning)
}

@Composable
expect fun RepeatablePredictiveBackHandler(
    repeatablePredictiveBackStateHolder: RepeatablePredictiveBackStateHolder,
    enabled: Boolean = true,
    onBack: () -> Unit,
)

@Composable
fun rememberCompletablePredictiveBackStateHolder(): CompletablePredictiveBackStateHolder =
    remember {
        CompletablePredictiveBackStateHolderImpl()
    }

sealed interface CompletablePredictiveBackStateHolder {
    val value: CompletablePredictiveBackState
}

internal class CompletablePredictiveBackStateHolderImpl : CompletablePredictiveBackStateHolder {
    override var value: CompletablePredictiveBackState by mutableStateOf(CompletablePredictiveBackState.NotRunning)
}

@Composable
expect fun CompletablePredictiveBackStateHandler(
    completablePredictiveBackStateHolder: CompletablePredictiveBackStateHolder,
    enabled: Boolean = true,
    onBack: () -> Unit,
)

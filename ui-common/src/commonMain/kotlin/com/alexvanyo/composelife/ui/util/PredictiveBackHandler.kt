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

/**
 * The state describing an in-progress predictive back animation.
 */
sealed interface PredictiveBackState {
    /**
     * There is no predictive back ongoing. On API 33 and below, this will always be the case.
     */
    data object NotRunning : PredictiveBackState

    /**
     * There is an ongoing predictive back animation, with the given [progress].
     */
    data class Running(
        val progress: Float,
    ) : PredictiveBackState
}

@Composable
expect fun predictiveBackHandler(
    enabled: Boolean = true,
    onBack: () -> Unit,
): PredictiveBackState

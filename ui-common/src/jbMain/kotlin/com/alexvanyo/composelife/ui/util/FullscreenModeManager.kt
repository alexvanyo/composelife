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

import androidx.compose.runtime.Stable
import kotlinx.coroutines.Deferred

/**
 * A manager that controls going fullscreen.
 */
@Stable
interface FullscreenModeManager {
    /**
     * True if the current state of the UI is immersive, meaning system UI is hidden
     */
    val isImmersive: Boolean

    /**
     * True if the current state of the UI is fullscreen, meaning the window is filling up the
     * entire display.
     */
    val isFullscreen: Boolean

    /**
     * Enters fullscreen mode. This method is fire-and-forget, and it will return a [Deferred]
     * that can be awaited to listen for the result of the request.
     */
    fun requestEnterFullscreenMode(): Deferred<Result<Unit>>

    /**
     * Exits fullscreen mode. This method is fire-and-forget, and it will return a [Deferred]
     * that can be awaited to listen for the result of the request.
     */
    fun requestExitFullscreenMode(): Deferred<Result<Unit>>
}

/**
 * Enters fullscreen mode. This method suspends, and returns a [Result] for whether the request succeeded.
 *
 * If the request failed or isn't supported, the returned [Result] will be a failure.
 */
suspend fun FullscreenModeManager.enterFullscreenMode(): Result<Unit> =
    requestEnterFullscreenMode().await()

/**
 * Exits fullscreen mode. This method suspends, and returns a [Result] for whether the request succeeded.
 *
 * If the request failed or isn't supported, the returned [Result] will be a failure.
 */
suspend fun FullscreenModeManager.exitFullscreenMode(): Result<Unit> =
    requestExitFullscreenMode().await()

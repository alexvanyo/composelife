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

import androidx.compose.ui.window.WindowPlacement
import androidx.compose.ui.window.WindowState
import com.alexvanyo.composelife.scopes.UiScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.awaitCancellation

@Inject
@ContributesBinding(UiScope::class)
class DesktopImmersiveModeManager(
    private val windowState: WindowState?,
) : ImmersiveModeManager {
    override suspend fun hideSystemUi() = awaitCancellation()

    override suspend fun enterFullscreenMode(): Result<Unit> =
        if (windowState == null) {
            Result.failure(IllegalStateException("No window state to control"))
        } else {
            windowState.placement = WindowPlacement.Fullscreen
            Result.success(Unit)
        }

    override suspend fun exitFullscreenMode(): Result<Unit> =
        if (windowState == null) {
            Result.failure(IllegalStateException("No window state to control"))
        } else {
            windowState.placement = WindowPlacement.Floating
            Result.success(Unit)
        }
}

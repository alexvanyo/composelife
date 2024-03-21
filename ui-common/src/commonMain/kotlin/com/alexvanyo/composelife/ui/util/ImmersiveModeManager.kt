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

import androidx.compose.runtime.Composable

/**
 * A manager that controls hiding the system UI.
 *
 * When the system UI should be hidden, call [hideSystemUi].
 */
interface ImmersiveModeManager {

    /**
     * Hides the system UI will called.
     *
     * This method won't finish normally. To stop hiding the system UI, cancel calling this function.
     */
    suspend fun hideSystemUi(): Nothing
}

@Composable
expect fun rememberImmersiveModeManager(): ImmersiveModeManager

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

import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.imeAnimationTarget
import androidx.compose.foundation.layout.imeAnimationSource
import androidx.compose.runtime.Composable
import com.livefront.sealedenum.SealedEnum

@OptIn(ExperimentalLayoutApi::class)
@Suppress("ComposeUnstableReceiver")
actual val WindowInsets.Companion.imeAnimationTarget: WindowInsets @Composable get() =
    WindowInsets.imeAnimationTarget

@OptIn(ExperimentalLayoutApi::class)
@Suppress("ComposeUnstableReceiver")
actual val WindowInsets.Companion.imeAnimationSource: WindowInsets @Composable get() =
    WindowInsets.imeAnimationSource

internal actual val LookaheadSafeDrawingHeightLayoutTypes.Companion._sealedEnum:
        SealedEnum<LookaheadSafeDrawingHeightLayoutTypes>
    get() = sealedEnum

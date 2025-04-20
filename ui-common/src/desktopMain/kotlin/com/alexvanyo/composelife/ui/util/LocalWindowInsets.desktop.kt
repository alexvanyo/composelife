/*
 * Copyright 2025 The Android Open Source Project
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

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.compositionLocalWithComputedDefaultOf
import androidx.compose.ui.Modifier

/**
 * A stub implementation for [ProvideLocalWindowInsetsHolder] that just relies on the default value of
 * [LocalWindowInsetsHolder] instead of providing an updated one.
 */
@Composable
actual fun ProvideLocalWindowInsetsHolder(
    modifier: Modifier,
    content: @Composable () -> Unit,
) {
    Box(
        propagateMinConstraints = true,
        modifier = modifier,
    ) {
        content()
    }
}

actual interface WindowInsetsHolder

/*
 * A [ProvidableCompositionLocal] for the [WindowInsetsCompat].
 *
 * Use [ProvideLocalWindowInsets] to update the [WindowInsetsCompat] appropriately.
 * If not used, the default [WindowShape] will be a simple rectangle path that matches the size of the window.
 */
actual val LocalWindowInsetsHolder: ProvidableCompositionLocal<WindowInsetsHolder> = compositionLocalWithComputedDefaultOf {
    object : WindowInsetsHolder {}
}

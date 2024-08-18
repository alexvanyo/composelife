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

package com.alexvanyo.composelife.ui.mobile

import android.os.Build
import androidx.annotation.ChecksSdkIntAtLeast
import androidx.compose.material3.ColorScheme
import androidx.compose.material3.darkColorScheme
import androidx.compose.material3.dynamicDarkColorScheme
import androidx.compose.material3.dynamicLightColorScheme
import androidx.compose.material3.lightColorScheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalContext

internal actual val ComposeLifeTheme.lightColorScheme: ColorScheme
    @Composable
    @ReadOnlyComposable
    get() =
        if (useDynamicColorScheme()) {
            dynamicLightColorScheme(LocalContext.current)
        } else {
            lightColorScheme()
        }

internal actual val ComposeLifeTheme.darkColorScheme: ColorScheme
    @Composable
    @ReadOnlyComposable
    get() =
        if (useDynamicColorScheme()) {
            dynamicDarkColorScheme(LocalContext.current)
        } else {
            darkColorScheme()
        }

@ChecksSdkIntAtLeast(api = 31)
private fun useDynamicColorScheme() =
    Build.VERSION.SDK_INT >= 31

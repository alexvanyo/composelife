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

package com.alexvanyo.composelife.ui.theme

import android.os.Build
import androidx.annotation.ChecksSdkIntAtLeast
import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Typography
import androidx.compose.material3.darkColorScheme
import androidx.compose.material3.dynamicDarkColorScheme
import androidx.compose.material3.dynamicLightColorScheme
import androidx.compose.material3.lightColorScheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.runtime.compositionLocalOf
import androidx.compose.ui.platform.LocalContext
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.entrypoints.preferences.inject

private val LocalAppliedComposeLifeTheme = compositionLocalOf { false }

@Composable
fun ComposeLifeTheme(
    darkTheme: Boolean = shouldUseDarkTheme(),
    content: @Composable () -> Unit,
) {
    if (LocalAppliedComposeLifeTheme.current) {
        content()
    } else {
        CompositionLocalProvider(LocalAppliedComposeLifeTheme provides true) {
            MaterialTheme(
                colorScheme = ComposeLifeTheme.colorScheme(darkTheme),
                typography = Typography(),
                content = content,
            )
        }
    }
}

object ComposeLifeTheme {

    @Composable
    fun colorScheme(darkTheme: Boolean) =
        if (darkTheme) {
            darkColorScheme
        } else {
            lightColorScheme
        }

    val lightColorScheme
        @Composable
        @ReadOnlyComposable
        get() =
            if (useDynamicColorScheme()) {
                dynamicLightColorScheme(LocalContext.current)
            } else {
                lightColorScheme()
            }

    val darkColorScheme
        @Composable
        @ReadOnlyComposable
        get() =
            if (useDynamicColorScheme()) {
                dynamicDarkColorScheme(LocalContext.current)
            } else {
                darkColorScheme()
            }

    val isLight
        @Composable
        @ReadOnlyComposable
        get() = MaterialTheme.colorScheme.surface == lightColorScheme.surface

    val aliveCellColor
        @Composable
        @ReadOnlyComposable
        get() = MaterialTheme.colorScheme.onSurface

    val deadCellColor
        @Composable
        @ReadOnlyComposable
        get() = MaterialTheme.colorScheme.surface
}

@ChecksSdkIntAtLeast(api = Build.VERSION_CODES.S)
private fun useDynamicColorScheme() =
    Build.VERSION.SDK_INT >= Build.VERSION_CODES.S

@Composable
private fun shouldUseDarkTheme(): Boolean =
    when (
        val darkThemeConfigState = inject().darkThemeConfigState
    ) {
        ResourceState.Loading,
        is ResourceState.Failure,
        -> isSystemInDarkTheme()
        is ResourceState.Success -> when (darkThemeConfigState.value) {
            DarkThemeConfig.FollowSystem -> isSystemInDarkTheme()
            DarkThemeConfig.Dark -> true
            DarkThemeConfig.Light -> false
        }
    }

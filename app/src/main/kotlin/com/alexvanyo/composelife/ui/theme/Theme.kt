package com.alexvanyo.composelife.ui.theme

import android.os.Build
import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Typography
import androidx.compose.material3.darkColorScheme
import androidx.compose.material3.dynamicDarkColorScheme
import androidx.compose.material3.dynamicLightColorScheme
import androidx.compose.material3.lightColorScheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalContext

@Composable
fun ComposeLifeTheme(
    darkTheme: Boolean = isSystemInDarkTheme(),
    content: @Composable () -> Unit,
) {
    MaterialTheme(
        colorScheme = ComposeLifeTheme.colorScheme(darkTheme),
        typography = Typography(),
        content = content
    )
}

object ComposeLifeTheme {

    @Composable
    @ReadOnlyComposable
    fun colorScheme(darkTheme: Boolean = isSystemInDarkTheme()) =
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

private fun useDynamicColorScheme() =
    Build.VERSION.SDK_INT >= Build.VERSION_CODES.S

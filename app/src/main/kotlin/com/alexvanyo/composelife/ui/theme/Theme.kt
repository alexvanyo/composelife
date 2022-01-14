package com.alexvanyo.composelife.ui.theme

import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.material.MaterialTheme
import androidx.compose.material.darkColors
import androidx.compose.material.lightColors
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.graphics.Color

private val DarkColorPalette = darkColors()

private val LightColorPalette = lightColors()

@Composable
fun ComposeLifeTheme(
    darkTheme: Boolean = isSystemInDarkTheme(),
    content: @Composable () -> Unit
) {
    val colors = if (darkTheme) {
        DarkColorPalette
    } else {
        LightColorPalette
    }

    MaterialTheme(
        colors = colors,
        typography = Typography,
        shapes = Shapes,
        content = content
    )
}

object ComposeLifeTheme {
    val aliveCellColor
        @Composable
        @ReadOnlyComposable
        get() = if (MaterialTheme.colors.isLight) {
            Color.Black
        } else {
            Color.White
        }

    val deadCellColor
        @Composable
        @ReadOnlyComposable
        get() = if (MaterialTheme.colors.isLight) {
            Color.White
        } else {
            Color.Black
        }
}

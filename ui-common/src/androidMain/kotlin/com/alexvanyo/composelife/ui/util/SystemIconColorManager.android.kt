package com.alexvanyo.composelife.ui.util

import android.app.Activity
import android.content.Context
import android.content.ContextWrapper
import android.view.Window
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalView
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.updatable.PowerableUpdatableWithMetadata
import com.alexvanyo.composelife.updatable.Updatable

interface SystemIconColorManager {

    suspend fun lightSystemBarIcons(): Nothing

    suspend fun darkSystemBarIcons(): Nothing
}

@Composable
fun rememberSystemIconColorManager(): SystemIconColorManager = rememberSystemIconColorManager(
    requireNotNull(LocalContext.current.findActivity()).window,
)

@Composable
fun rememberSystemIconColorManager(
    window: Window,
): SystemIconColorManager {
    val view = LocalView.current

    val systemIconColorManager = remember(window, view) {
        val windowInsetsControllerCompat = WindowInsetsControllerCompat(window, view)
        AndroidSystemIconColorManager(
            windowInsetsControllerCompat,
        )
    }

    LaunchedEffect(systemIconColorManager) {
        systemIconColorManager.update()
    }

    return systemIconColorManager
}

private class AndroidSystemIconColorManager private constructor(
    private val powerableUpdatableWithMetadata: PowerableUpdatableWithMetadata<Boolean>,
) : SystemIconColorManager, Updatable by powerableUpdatableWithMetadata {
    constructor(
        windowInsetsControllerCompat: WindowInsetsControllerCompat,
    ) : this(
        PowerableUpdatableWithMetadata { metadata ->
            val initialStatusBarColor = windowInsetsControllerCompat.isAppearanceLightStatusBars
            val initialNavigationBarColor = windowInsetsControllerCompat.isAppearanceLightNavigationBars

            try {
                metadata
                    .collect {
                        if (it.isNotEmpty()) {
                            windowInsetsControllerCompat.isAppearanceLightStatusBars = it.last()
                            windowInsetsControllerCompat.isAppearanceLightNavigationBars = it.last()
                        }
                    }
            } finally {
                windowInsetsControllerCompat.isAppearanceLightStatusBars = initialStatusBarColor
                windowInsetsControllerCompat.isAppearanceLightNavigationBars = initialNavigationBarColor
            }
        },
    )

    override suspend fun lightSystemBarIcons(): Nothing = powerableUpdatableWithMetadata.press(true)

    override suspend fun darkSystemBarIcons(): Nothing = powerableUpdatableWithMetadata.press(false)
}

private tailrec fun Context.findActivity(): Activity? {
    return when (this) {
        is Activity -> this
        is ContextWrapper -> this.baseContext.findActivity()
        else -> null
    }
}

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

import android.app.Activity
import android.content.Context
import android.content.ContextWrapper
import android.view.Window
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalView
import androidx.core.view.WindowInsetsCompat
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.updatable.PowerableUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation

@Composable
actual fun rememberImmersiveModeManager(): ImmersiveModeManager = rememberImmersiveModeManager(
    requireNotNull(LocalContext.current.findActivity()).window,
)

@Composable
fun rememberImmersiveModeManager(
    window: Window,
): ImmersiveModeManager {
    val view = LocalView.current

    val immersiveModeManager = remember(window, view) {
        val windowInsetsControllerCompat = WindowInsetsControllerCompat(window, view)
        AndroidImmersiveModeManager(
            windowInsetsControllerCompat,
        )
    }

    LaunchedEffect(immersiveModeManager) {
        immersiveModeManager.update()
    }

    return immersiveModeManager
}

private class AndroidImmersiveModeManager private constructor(
    private val powerableUpdatable: PowerableUpdatable,
) : ImmersiveModeManager, Updatable by powerableUpdatable {
    constructor(
        windowInsetsControllerCompat: WindowInsetsControllerCompat,
    ) : this(
        PowerableUpdatable {
            try {
                windowInsetsControllerCompat.hide(WindowInsetsCompat.Type.systemBars())
                awaitCancellation()
            } finally {
                windowInsetsControllerCompat.show(WindowInsetsCompat.Type.systemBars())
            }
        },
    )

    override suspend fun hideSystemUi() = powerableUpdatable.press()
}

private tailrec fun Context.findActivity(): Activity? {
    return when (this) {
        is Activity -> this
        is ContextWrapper -> this.baseContext.findActivity()
        else -> null
    }
}

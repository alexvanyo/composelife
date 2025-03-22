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
import android.os.Build
import android.os.OutcomeReceiver
import android.view.Window
import androidx.activity.compose.LocalActivity
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.platform.LocalView
import androidx.core.view.WindowInsetsCompat
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.updatable.PowerableUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.suspendCancellableCoroutine

@Composable
actual fun rememberImmersiveModeManager(): ImmersiveModeManager = rememberImmersiveModeManager(
    activity = requireNotNull(LocalActivity.current),
    window = requireNotNull(LocalActivity.current).window,
)

@Composable
fun rememberImmersiveModeManager(
    activity: Activity,
    window: Window,
): ImmersiveModeManager {
    val view = LocalView.current

    val immersiveModeManager = remember(activity, window, view) {
        val windowInsetsControllerCompat = WindowInsetsControllerCompat(window, view)
        AndroidImmersiveModeManager(
            activity,
            windowInsetsControllerCompat,
        )
    }

    LaunchedEffect(immersiveModeManager) {
        immersiveModeManager.update()
    }

    return immersiveModeManager
}

private class AndroidImmersiveModeManager private constructor(
    private val activity: Activity,
    private val powerableUpdatable: PowerableUpdatable,
) : ImmersiveModeManager, Updatable by powerableUpdatable {
    constructor(
        activity: Activity,
        windowInsetsControllerCompat: WindowInsetsControllerCompat,
    ) : this(
        activity,
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

    override suspend fun enterFullscreenMode(): Result<Unit> =
        if (Build.VERSION.SDK_INT >= 35) {
            suspendCancellableCoroutine { cont ->
                activity.requestFullscreenMode(
                    Activity.FULLSCREEN_MODE_REQUEST_ENTER,
                    @Suppress("ForbiddenVoid")
                    object : OutcomeReceiver<Void, Throwable> {
                        override fun onResult(result: Void?) {
                            cont.resume(Result.success(Unit)) { _, _, _ -> }
                        }

                        override fun onError(error: Throwable) {
                            cont.resume(Result.failure(error)) { _, _, _ -> }
                        }
                    },
                )
            }
        } else {
            Result.failure(IllegalStateException("Not supported on API < 35"))
        }

    override suspend fun exitFullscreenMode(): Result<Unit> =
        if (Build.VERSION.SDK_INT >= 35) {
            suspendCancellableCoroutine { cont ->
                activity.requestFullscreenMode(
                    Activity.FULLSCREEN_MODE_REQUEST_EXIT,
                    @Suppress("ForbiddenVoid")
                    object : OutcomeReceiver<Void, Throwable> {
                        override fun onResult(result: Void?) {
                            cont.resume(Result.success(Unit)) { _, _, _ -> }
                        }

                        override fun onError(error: Throwable) {
                            cont.resume(Result.failure(error)) { _, _, _ -> }
                        }
                    },
                )
            }
        } else {
            Result.failure(IllegalStateException("Not supported on API < 35"))
        }
}

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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.core.view.WindowCompat
import androidx.core.view.WindowInsetsCompat
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesIntoSet
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.Deferred
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.suspendCancellableCoroutine
import kotlinx.coroutines.withContext

@SingleIn(UiScope::class)
@ContributesBinding(UiScope::class, binding = binding<FullscreenModeManager>())
@ContributesIntoSet(UiScope::class, binding = binding<
    @ForScope(UiScope::class)
    Updatable,
    >())
@Inject
class AndroidFullscreenModeManager(
    private val activity: Activity?,
    private val windowInsetsControllerCompat: WindowInsetsControllerCompat?,
    private val dispatchers: ComposeLifeDispatchers,
) : FullscreenModeManager, Updatable {

    private var _isImmersive by mutableStateOf(false)

    override var isImmersive: Boolean
        get() = _isImmersive
        private set(value) {
            _isImmersive = value
            if (value) {
                windowInsetsControllerCompat?.hide(WindowInsetsCompat.Type.systemBars())
            } else {
                windowInsetsControllerCompat?.show(WindowInsetsCompat.Type.systemBars())
            }
        }

    override var isFullscreen: Boolean by mutableStateOf(false)
        private set

    override fun requestEnterFullscreenMode(): Deferred<Result<Unit>> {
        val completableDeferred = CompletableDeferred<Result<Unit>>()
        requests.trySend(Request(RequestType.EnterFullscreen, completableDeferred))
        return completableDeferred
    }

    override fun requestExitFullscreenMode(): Deferred<Result<Unit>> {
        val completableDeferred = CompletableDeferred<Result<Unit>>()
        requests.trySend(Request(RequestType.ExitFullscreen, completableDeferred))
        return completableDeferred
    }

    override suspend fun update(): Nothing =
        coroutineScope {
            // TODO: Register for multi window mode changes to update isFullscreen and isImmersive
            launch { actor() }
            awaitCancellation()
        }

    private suspend fun actor(): Nothing {
        requests.receiveAsFlow().collect { request ->
            when (request.type) {
                RequestType.EnterFullscreen -> request.completableDeferred.complete(
                    enterFullscreenMode(),
                )
                RequestType.ExitFullscreen -> request.completableDeferred.complete(
                    exitFullscreenMode(),
                )
            }
        }
        awaitCancellation()
    }

    private val requests = Channel<Request>(capacity = Channel.UNLIMITED)

    private data class Request(
        val type: RequestType,
        val completableDeferred: CompletableDeferred<Result<Unit>>,
    )

    private sealed interface RequestType {
        data object EnterFullscreen : RequestType
        data object ExitFullscreen : RequestType
    }

    private suspend fun enterFullscreenMode(): Result<Unit> =
        if (activity == null) {
            isFullscreen = false
            Result.failure(IllegalStateException("No Activity to request fullscreen with"))
        } else if (Build.VERSION.SDK_INT >= 35) {
            suspendCancellableCoroutine { cont ->
                activity.requestFullscreenMode(
                    Activity.FULLSCREEN_MODE_REQUEST_ENTER,
                    @Suppress("ForbiddenVoid")
                    object : OutcomeReceiver<Void, Throwable> {
                        override fun onResult(result: Void?) {
                            isFullscreen = true
                            cont.resume(Result.success(Unit)) { _, _, _ -> }
                        }

                        override fun onError(error: Throwable) {
                            isFullscreen = false
                            cont.resume(Result.failure(error)) { _, _, _ -> }
                        }
                    },
                )
            }
        } else {
            isFullscreen = false
            Result.failure(IllegalStateException("Not supported on API < 35"))
        }.also {
            withContext(dispatchers.Main) {
                isImmersive = true
            }
        }

    private suspend fun exitFullscreenMode(): Result<Unit> =
        if (activity == null) {
            isFullscreen = false
            Result.failure(IllegalStateException("No Activity to request fullscreen with"))
        } else if (Build.VERSION.SDK_INT >= 35) {
            suspendCancellableCoroutine { cont ->
                activity.requestFullscreenMode(
                    Activity.FULLSCREEN_MODE_REQUEST_EXIT,
                    @Suppress("ForbiddenVoid")
                    object : OutcomeReceiver<Void, Throwable> {
                        override fun onResult(result: Void?) {
                            isFullscreen = false
                            cont.resume(Result.success(Unit)) { _, _, _ -> }
                        }

                        override fun onError(error: Throwable) {
                            isFullscreen = false
                            cont.resume(Result.failure(error)) { _, _, _ -> }
                        }
                    },
                )
            }
        } else {
            isFullscreen = false
            Result.failure(IllegalStateException("Not supported on API < 35"))
        }.also {
            withContext(dispatchers.Main) {
                isImmersive = false
            }
        }
}

@ContributesTo(UiScope::class)
@BindingContainer
interface WindowInsetsControllerBindings {
    companion object {
        @Provides
        @SingleIn(UiScope::class)
        fun providesWindowInsetsController(
            window: Window?,
        ): WindowInsetsControllerCompat? =
            window?.let { WindowCompat.getInsetsController(window, window.decorView) }
    }
}

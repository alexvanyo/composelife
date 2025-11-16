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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.Deferred
import kotlinx.coroutines.await
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.consumeAsFlow
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.launch
import org.w3c.dom.Document
import org.w3c.dom.Element
import org.w3c.dom.events.Event
import kotlin.coroutines.cancellation.CancellationException

@ContributesTo(UiScope::class)
@BindingContainer
interface WebImmersiveModeManagerBindings {
    @Binds
    val WebFullscreenModeManager.bind: FullscreenModeManager

    @Binds
    @IntoSet
    @ForScope(UiScope::class)
    val WebFullscreenModeManager.bindIntoUpdatable: Updatable
}

@SingleIn(UiScope::class)
@Inject
class WebFullscreenModeManager(
    val element: Element,
    val document: Document,
) : FullscreenModeManager, Updatable {
    override val isImmersive: Boolean
        get() = false

    override var isFullscreen: Boolean by mutableStateOf(document.fullscreenElement != null)
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

    override suspend fun update(): Nothing = coroutineScope {
        launch { observeFullscreenChanges() }
        launch { actor() }
        awaitCancellation()
    }

    private suspend fun observeFullscreenChanges(): Nothing {
        val listener: (Event) -> Unit = { _ ->
            isFullscreen = document.fullscreenElement != null
        }
        try {
            element.addEventListener("fullscreenchange", listener)
            awaitCancellation()
        } finally {
            element.removeEventListener("fullscreenchange", listener)
        }
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

    @OptIn(ExperimentalWasmJsInterop::class)
    private suspend fun enterFullscreenMode(): Result<Unit> =
        element.requestFullscreen().runSuspendCatching {
            await()
        }

    @OptIn(ExperimentalWasmJsInterop::class)
    private suspend fun exitFullscreenMode(): Result<Unit> =
        document.exitFullscreen().runSuspendCatching {
            await()
        }
}

@Suppress("TooGenericExceptionCaught")
suspend inline fun <R> runSuspendCatching(block: () -> R): Result<R> =
    try {
        Result.success(block())
    } catch (c: CancellationException) {
        throw c
    } catch (e: Throwable) {
        Result.failure(e)
    }

@Suppress("TooGenericExceptionCaught")
suspend inline fun <T, R> T.runSuspendCatching(block: T.() -> R): Result<R> =
    try {
        Result.success(block())
    } catch (c: CancellationException) {
        throw c
    } catch (e: Throwable) {
        Result.failure(e)
    }

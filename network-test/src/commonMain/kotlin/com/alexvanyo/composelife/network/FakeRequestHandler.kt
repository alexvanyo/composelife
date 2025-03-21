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

package com.alexvanyo.composelife.network

import io.ktor.client.engine.mock.MockRequestHandler
import kotlinx.coroutines.channels.Channel
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

/**
 * The singleton fake request handler for a [io.ktor.client.engine.mock.MockEngine].
 *
 * The [MockRequestHandler] returned from [asMockRequestHandler] will receive from an internal unlimited channel,
 * populated by [addRequestHandler].
 */
@Inject
@SingleIn(AppScope::class)
class FakeRequestHandler {
    private val handlers = Channel<MockRequestHandler>(capacity = Channel.UNLIMITED)

    /**
     * Returns a [MockRequestHandler] that pulls from [handlers] to handle the request
     */
    internal fun asMockRequestHandler(): MockRequestHandler = { request ->
        handlers.receive().invoke(this, request)
    }

    /**
     * Adds the [mockRequestHandler] to the queue of [MockRequestHandler]s used to respond to requests.
     */
    fun addRequestHandler(mockRequestHandler: MockRequestHandler) {
        handlers.trySend(mockRequestHandler)
    }
}

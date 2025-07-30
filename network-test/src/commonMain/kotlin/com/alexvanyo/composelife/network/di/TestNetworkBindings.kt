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

package com.alexvanyo.composelife.network.di

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.network.FakeRequestHandler
import com.alexvanyo.composelife.updatable.AppUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import io.ktor.client.HttpClient
import io.ktor.client.engine.mock.MockEngine
import kotlinx.coroutines.awaitCancellation

@ContributesTo(AppScope::class, replaces = [NetworkBindings::class])
@BindingContainer
interface TestNetworkBindings {
    companion object {
        @SingleIn(AppScope::class)
        @Provides
        fun providesHttpClient(
            dispatchers: ComposeLifeDispatchers,
            fakeRequestHandler: FakeRequestHandler,
        ): HttpClient =
            HttpClient(MockEngine) {
                expectSuccess = true
                engine {
                    addHandler(fakeRequestHandler.asMockRequestHandler())
                    dispatcher = dispatchers.IOWithLimitedParallelism(1)
                }
            }

        @Provides
        @SingleIn(AppScope::class)
        @IntoSet
        @AppUpdatable
        fun providesHttpClientClosingIntoUpdatable(
            httpClient: HttpClient,
        ): Updatable = object : Updatable {
            override suspend fun update(): Nothing =
                httpClient.use { _ ->
                    awaitCancellation()
                }
        }
    }
}

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
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.network.EngineFactoryWithConfigBlock
import com.alexvanyo.composelife.network.HttpClient
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ExperimentalMetroApi
import dev.zacsweers.metro.OnGraphClose
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import io.ktor.client.HttpClient
import io.ktor.client.plugins.logging.Logging

@ContributesTo(AppScope::class)
@BindingContainer
interface NetworkBindings {
    companion object {
        @SingleIn(AppScope::class)
        @Provides
        internal fun providesHttpClient(
            dispatchers: ComposeLifeDispatchers,
            logger: Logger,
            engineFactoryWithConfigBlock: EngineFactoryWithConfigBlock<*>,
        ): HttpClient = HttpClient(engineFactoryWithConfigBlock) {
            engine {
                dispatcher = dispatchers.IOWithLimitedParallelism(4)
            }
            install(Logging) {
                this.logger = object : io.ktor.client.plugins.logging.Logger {
                    override fun log(message: String) = logger.d(tag = "HttpClient", message = { message })
                }
            }
        }
    }
}

@OptIn(ExperimentalMetroApi::class)
@ContributesTo(AppScope::class)
interface HttpClientLifecycle {
    @OnGraphClose
    fun closeHttpClient(httpClient: Lazy<HttpClient>) {
        if (httpClient.isInitialized()) {
            httpClient.value.close()
        }
    }
}

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

import io.ktor.client.HttpClient
import io.ktor.client.HttpClientConfig
import io.ktor.client.engine.HttpClientEngineConfig
import io.ktor.client.engine.HttpClientEngineFactory

class EngineFactoryWithConfigBlock<T : HttpClientEngineConfig>(
    val engineFactory: HttpClientEngineFactory<T>,
    val block: HttpClientConfig<T>.() -> Unit,
)

fun <T : HttpClientEngineConfig> HttpClient(
    engineFactoryWithConfig: EngineFactoryWithConfigBlock<T>,
    block: HttpClientConfig<T>.() -> Unit,
): HttpClient =
    HttpClient(
        engineFactoryWithConfig.engineFactory,
    ) {
        engineFactoryWithConfig.block(this)
        block()
    }

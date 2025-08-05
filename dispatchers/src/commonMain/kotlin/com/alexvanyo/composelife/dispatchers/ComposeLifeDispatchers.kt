/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlin.coroutines.CoroutineContext

/**
 * A custom interface version of [Dispatchers], so that dispatchers can be injected.
 */
@Suppress("VariableNaming")
interface ComposeLifeDispatchers {
    /**
     * @see Dispatchers.Default
     */
    val Default: CoroutineContext

    /**
     * @see Dispatchers.Main
     */
    val Main: CoroutineContext

    /**
     * @see Dispatchers.Main.immediate
     */
    val MainImmediate: CoroutineContext

    /**
     * @see Dispatchers.Unconfined
     */
    val Unconfined: CoroutineContext

    /**
     * @see Dispatchers.IO
     */
    val IO: CoroutineContext

    /**
     * Returns an injectable version of `Dispatchers.IO.limitedParallelism(parallelism)`
     */
    fun IOWithLimitedParallelism(parallelism: Int): CoroutineDispatcher

    /**
     * The [CoroutineContext] for driving cell state ticks, in response to time delays.
     */
    val CellTicker: CoroutineContext
}

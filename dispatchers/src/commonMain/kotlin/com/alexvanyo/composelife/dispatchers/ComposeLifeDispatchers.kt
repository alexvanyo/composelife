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

import kotlinx.coroutines.Dispatchers
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

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
     * @see Dispatchers.Unconfined
     */
    val Unconfined: CoroutineContext

    /**
     * @see Dispatchers.IO
     */
    val IO: CoroutineContext

    /**
     * The [CoroutineContext] for driving cell state ticks, in response to time delays.
     */
    val CellTicker: CoroutineContext
}

/**
 * The default implementation of [ComposeLifeDispatchers], which just delegates to the normal [Dispatchers] versions.
 */
@Suppress("InjectDispatcher")
@Inject
@ContributesBinding(AppScope::class)
@SingleIn(AppScope::class)
class DefaultComposeLifeDispatchers : ComposeLifeDispatchers {
    override val Default: CoroutineContext = Dispatchers.Default
    override val Main: CoroutineContext = Dispatchers.Main
    override val Unconfined: CoroutineContext = Dispatchers.Unconfined
    override val IO: CoroutineContext = Dispatchers.IO
    override val CellTicker: CoroutineContext = EmptyCoroutineContext
}

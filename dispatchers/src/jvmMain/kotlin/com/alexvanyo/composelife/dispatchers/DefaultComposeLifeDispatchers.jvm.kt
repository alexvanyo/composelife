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

package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.SingleIn
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * The default implementation of [ComposeLifeDispatchers], which just delegates to the normal [Dispatchers] versions.
 */
@Inject
@ContributesBinding(AppScope::class)
@SingleIn(AppScope::class)
class DefaultComposeLifeDispatchers : ComposeLifeDispatchers {
    override val Default: CoroutineContext = Dispatchers.Default
    override val Main: CoroutineContext = Dispatchers.Main
    override val Unconfined: CoroutineContext = Dispatchers.Unconfined
    override val IO: CoroutineContext = Dispatchers.IO
    override fun IOWithLimitedParallelism(parallelism: Int): CoroutineDispatcher =
        Dispatchers.IO.limitedParallelism(parallelism)
    override val CellTicker: CoroutineContext = EmptyCoroutineContext
}

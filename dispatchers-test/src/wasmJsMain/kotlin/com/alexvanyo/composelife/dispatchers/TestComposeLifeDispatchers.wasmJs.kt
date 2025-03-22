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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.test.TestDispatcher
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.SingleIn
import kotlin.coroutines.CoroutineContext

/**
 * A test implementation of [ComposeLifeDispatchers], which delegates [Default], [Main] and [IO] to the provided
 * [TestDispatcher].
 *
 * [Unconfined] delegates to the default implementations, due to their custom behavior.
 */
@Inject
@ContributesBinding(AppScope::class, replaces = [DefaultComposeLifeDispatchers::class])
@SingleIn(AppScope::class)
actual class TestComposeLifeDispatchers actual constructor(
    @GeneralTestDispatcher private val generalTestDispatcher: TestDispatcher,
    @CellTickerTestDispatcher cellTickerTestDispatcher: TestDispatcher,
) : ComposeLifeDispatchers {
    override val Default: CoroutineContext = generalTestDispatcher
    override val Main: CoroutineContext = generalTestDispatcher
    override val Unconfined: CoroutineContext = Dispatchers.Unconfined
    override val IO: CoroutineContext = generalTestDispatcher
    override fun IOWithLimitedParallelism(parallelism: Int): CoroutineDispatcher =
        generalTestDispatcher.limitedParallelism(parallelism)
    override val CellTicker: CoroutineContext = cellTickerTestDispatcher

    companion object
}

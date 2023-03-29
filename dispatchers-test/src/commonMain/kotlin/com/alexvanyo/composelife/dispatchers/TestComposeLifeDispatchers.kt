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
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Inject

/**
 * A test implementation of [ComposeLifeDispatchers], which delegates [Default], [Main] and [IO] to the provided
 * [TestDispatcher].
 *
 * [Unconfined] delegates to the default implementations, due to their custom behavior.
 */
@Suppress("InjectDispatcher")
@OptIn(ExperimentalCoroutinesApi::class)
class TestComposeLifeDispatchers @Inject constructor(
    testDispatcher: TestDispatcher,
) : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = testDispatcher
    override val Main: CoroutineDispatcher = testDispatcher
    override val Unconfined: CoroutineDispatcher = Dispatchers.Unconfined
    override val IO: CoroutineDispatcher = testDispatcher
}

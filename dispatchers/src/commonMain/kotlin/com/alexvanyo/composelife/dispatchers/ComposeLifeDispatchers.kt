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
import kotlinx.coroutines.MainCoroutineDispatcher
import javax.inject.Inject

/**
 * A custom interface version of [Dispatchers], so that dispatchers can be injected.
 */
@Suppress("VariableNaming")
interface ComposeLifeDispatchers {
    /**
     * @see Dispatchers.Default
     */
    val Default: CoroutineDispatcher

    /**
     * @see Dispatchers.Main
     */
    val Main: CoroutineDispatcher

    /**
     * @see Dispatchers.Unconfined
     */
    val Unconfined: CoroutineDispatcher

    /**
     * @see Dispatchers.IO
     */
    val IO: CoroutineDispatcher
}

/**
 * The default implementation of [ComposeLifeDispatchers], which just delegates to the normal [Dispatchers] versions.
 */
@Suppress("InjectDispatcher")
class DefaultComposeLifeDispatchers @Inject constructor() : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = Dispatchers.Default
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = Dispatchers.Unconfined
    override val IO: CoroutineDispatcher = Dispatchers.IO
}

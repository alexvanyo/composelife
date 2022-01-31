package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.MainCoroutineDispatcher
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Inject

/**
 * A test implementation of [ComposeLifeDispatchers], which delegates [Default] and [IO] to the provided
 * [TestDispatcher].
 *
 * [Main] and [Unconfined] delegate to the default implementations, due to their custom behavior.
 *
 * To use [TestDispatcher] as [Dispatchers.Main], use [Dispatchers.setMain].
 */
@OptIn(ExperimentalCoroutinesApi::class)
class TestComposeLifeDispatchers @Inject constructor(
    testDispatcher: TestDispatcher,
) : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = testDispatcher
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = Dispatchers.Unconfined
    override val IO: CoroutineDispatcher = testDispatcher
}

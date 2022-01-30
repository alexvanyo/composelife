package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.MainCoroutineDispatcher
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
class TestComposeLifeDispatchers @Inject constructor(
    testDispatcher: TestDispatcher,
) : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = testDispatcher
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = testDispatcher
    override val IO: CoroutineDispatcher = testDispatcher
}

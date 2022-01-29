package com.alexvanyo.composelife.testutil

import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.MainCoroutineDispatcher
import kotlinx.coroutines.test.TestDispatcher

@OptIn(ExperimentalCoroutinesApi::class)
class TestComposeLifeDispatchers(
    testCoroutineDispatcher: TestDispatcher,
) : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = testCoroutineDispatcher
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = testCoroutineDispatcher
    override val IO: CoroutineDispatcher = testCoroutineDispatcher
}

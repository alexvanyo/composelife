package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.MainCoroutineDispatcher
import javax.inject.Inject

@Suppress("VariableNaming")
interface ComposeLifeDispatchers {
    val Default: CoroutineDispatcher
    val Main: MainCoroutineDispatcher
    val Unconfined: CoroutineDispatcher
    val IO: CoroutineDispatcher
}

class DefaultComposeLifeDispatchers @Inject constructor() : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = Dispatchers.Default
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = Dispatchers.Unconfined
    override val IO: CoroutineDispatcher = Dispatchers.IO
}

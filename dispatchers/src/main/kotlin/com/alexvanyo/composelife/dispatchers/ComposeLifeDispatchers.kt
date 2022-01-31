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
    val Main: MainCoroutineDispatcher

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
class DefaultComposeLifeDispatchers @Inject constructor() : ComposeLifeDispatchers {
    override val Default: CoroutineDispatcher = Dispatchers.Default
    override val Main: MainCoroutineDispatcher = Dispatchers.Main
    override val Unconfined: CoroutineDispatcher = Dispatchers.Unconfined
    override val IO: CoroutineDispatcher = Dispatchers.IO
}

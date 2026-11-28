/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.test

import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ForScope
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runTest
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

interface BaseInjectTestCtx {
    @GeneralTestDispatcher val generalTestDispatcher: TestDispatcher

    @ForScope(AppScope::class)
    val appUpdatables: Set<Updatable>
}

@Suppress("AbstractClassCanBeConcreteClass")
expect abstract class BaseInjectTest<G>(applicationGraphCreator: (ApplicationGraphArguments) -> G) :
    BaseInjectTestImpl<G>
    where G : ApplicationGraph, G : BaseInjectTestCtx

/**
 * A base class for testing components that depend on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass", "AbstractClassCanBeConcreteClass")
abstract class BaseInjectTestImpl<G>(applicationGraphCreator: (ApplicationGraphArguments) -> G) :
    BaseKmpTest()
    where G : ApplicationGraph, G : BaseInjectTestCtx {
    val applicationGraph: G = applicationGraphCreator(createApplicationGraphArguments())

    internal val appUpdatables: Set<Updatable> get() = applicationGraph.appUpdatables
    internal val generalTestDispatcher: TestDispatcher get() = applicationGraph.generalTestDispatcher

    @OptIn(ExperimentalCoroutinesApi::class)
    open fun runAppTest(
        context: CoroutineContext = EmptyCoroutineContext,
        timeout: Duration = 60.seconds,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = runTest(
        context = generalTestDispatcher + context,
        timeout = timeout,
    ) {
        try {
            withUpdatables(appUpdatables) {
                // Let any background jobs launch and stabilize before running the test body
                advanceUntilIdle()
                testBody()
            }
        } finally {
            applicationGraph.close()
        }
    }
}

suspend fun withUpdatables(updatables: Set<Updatable>, testBody: suspend () -> Unit): Unit = coroutineScope {
    val backgroundJob = launch {
        updatables.forEach { updatable ->
            launch {
                updatable.update()
            }
        }
    }
    try {
        testBody()
    } finally {
        backgroundJob.cancelAndJoin()
    }
}

expect fun createApplicationGraphArguments(): ApplicationGraphArguments

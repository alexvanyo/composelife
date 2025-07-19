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

import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.ApplicationComponentArguments
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

@ContributesTo(AppScope::class)
interface BaseInjectTestEntryPoint {
    val updatables: Set<Updatable>
}

expect abstract class BaseInjectTest(
    applicationComponentCreator: (ApplicationComponentArguments) -> ApplicationComponent,
) : BaseInjectTestImpl

/**
 * A base class for testing components that depend on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass")
abstract class BaseInjectTestImpl(
    applicationComponentCreator: (ApplicationComponentArguments) -> ApplicationComponent,
) {
    val applicationComponent = applicationComponentCreator(createApplicationComponentArguments())

    // TODO: Replace with applicationComponent.asContribution<BaseInjectTestEntryPoint>()
    private val entryPoint get() = applicationComponent as BaseInjectTestEntryPoint

    private val updatables: Set<Updatable>
        get() = entryPoint.updatables

    @OptIn(ExperimentalCoroutinesApi::class)
    fun runAppTest(
        context: CoroutineContext = EmptyCoroutineContext,
        timeout: Duration = 60.seconds,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = runTest(
        context = context,
        timeout = timeout,
    ) {
        withAppTestDependencies {
            // Let any background jobs launch and stabilize before running the test body
            advanceUntilIdle()
            testBody()
        }
    }

    suspend fun withAppTestDependencies(
        testBody: suspend () -> Unit,
    ): Unit = coroutineScope {
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
}

expect fun createApplicationComponentArguments(): ApplicationComponentArguments

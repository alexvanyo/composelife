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

import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.cancelAndJoin
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

@EntryPoint(AppScope::class)
interface BaseInjectTestEntryPoint : UpdatableModule

/**
 * A base class for testing components that depend on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass")
@RunWith(KmpAndroidJUnit4::class)
abstract class BaseInjectTest<AC : ApplicationComponent>(
    applicationComponentCreator: () -> AC,
) {
    val applicationComponent = applicationComponentCreator()

    private val entryPoint get() = applicationComponent.kmpGetEntryPoint<BaseInjectTestEntryPoint>()

    private val updatables: Set<Updatable>
        get() = entryPoint.updatables

    fun runAppTest(
        context: CoroutineContext = EmptyCoroutineContext,
        timeout: Duration = 60.seconds,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = runTest(
        context = context,
        timeout = timeout,
    ) {
        withAppTestDependencies {
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

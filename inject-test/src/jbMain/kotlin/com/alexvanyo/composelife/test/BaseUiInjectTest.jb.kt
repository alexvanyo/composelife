/*
 * Copyright 2024 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.test

import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.updatable.UiUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.ContributesTo
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.coroutines.coroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

@ContributesTo(UiScope::class)
interface BaseUiInjectTestEntryPoint {
    @UiUpdatable val uiUpdatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val UiGraph.baseUiInjectTestEntryPoint: BaseUiInjectTestEntryPoint get() =
    this as BaseUiInjectTestEntryPoint

/**
 * A base class for testing UI that depends on injected classes.
 *
 * Subclasses must call [runUiTest] instead of [runAppTest] or [runAppTest] to properly initialize dependencies.
 */
abstract class BaseUiInjectTest(
    applicationGraphCreator: (ApplicationGraphArguments) -> ApplicationGraph,
) : BaseInjectTest(applicationGraphCreator) {
    internal val uiGraphCreator: UiGraph.Factory get() =
        applicationGraph as UiGraph.Factory

    @Deprecated("Testing with BaseUiInjectTest should call runUiTest instead of runAppTest")
    override fun runAppTest(
        context: CoroutineContext,
        timeout: Duration,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = super.runAppTest(context, timeout, testBody)
}

@OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
fun BaseUiInjectTest.runUiTest(
    appTestContext: CoroutineContext = EmptyCoroutineContext,
    timeout: Duration = 60.seconds,
    testBody: suspend ComposeUiTest.(uiGraph: UiGraph) -> Unit,
): TestResult =
    runPlatformUiTest(
        runTestContext = generalTestDispatcher + appTestContext,
        timeout = timeout,
    ) { uiGraphArguments ->
        val uiGraph = uiGraphCreator.create(uiGraphArguments)
        val uiUpdatables = uiGraph.baseUiInjectTestEntryPoint.uiUpdatables
        withUpdatables(appUpdatables + uiUpdatables) {
            // Let any background jobs launch and stabilize before running the test body
            val testDispatcher = coroutineContext[CoroutineDispatcher] as? TestDispatcher
            testDispatcher?.scheduler?.advanceUntilIdle()
            testBody(
                this@runPlatformUiTest,
                uiGraph,
            )
        }
    }

@OptIn(ExperimentalTestApi::class)
internal expect fun runPlatformUiTest(
    runTestContext: CoroutineContext,
    timeout: Duration,
    testBody: suspend ComposeUiTest.(uiGraphArguments: UiGraphArguments) -> Unit,
): TestResult

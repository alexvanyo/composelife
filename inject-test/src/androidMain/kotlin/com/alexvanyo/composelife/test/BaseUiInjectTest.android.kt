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

package com.alexvanyo.composelife.test

import androidx.activity.ComponentActivity
import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runAndroidComposeUiTest
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.TestResult
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.coroutineContext
import kotlin.time.Duration

@OptIn(ExperimentalTestApi::class)
actual fun BaseUiInjectTest.runUiTest(
    appTestContext: CoroutineContext,
    timeout: Duration,
    testBody: suspend ComposeUiTest.(uiGraph: UiGraph) -> Unit,
): TestResult =
    runAndroidComposeUiTest<ComponentActivity>(
        runTestContext = generalTestDispatcher + appTestContext,
        testTimeout = timeout,
    ) {
        val uiGraph = uiGraphCreator.create(
            object : UiGraphArguments {
                override val activity = requireNotNull(this@runAndroidComposeUiTest.activity)
                override val uiContext = activity
            },
        )
        val uiUpdatables = uiGraph.baseUiInjectTestEntryPoint.uiUpdatables
        withUpdatables(appUpdatables + uiUpdatables) {
            // Let any background jobs launch and stabilize before running the test body
            val testDispatcher = coroutineContext[CoroutineDispatcher] as? TestDispatcher
            testDispatcher?.scheduler?.advanceUntilIdle()
            testBody(
                this@runAndroidComposeUiTest,
                uiGraph,
            )
        }
    }

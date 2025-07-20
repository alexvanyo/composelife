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

import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.runCurrent
import kotlin.coroutines.CoroutineContext
import kotlin.time.Duration

@OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
actual fun BaseUiInjectTest.runUiTest(
    appTestContext: CoroutineContext,
    timeout: Duration,
    testBody: suspend ComposeUiTest.(uiGraph: UiGraph) -> Unit,
): TestResult =
    runComposeUiTest {
        val uiGraph = uiGraphCreator.create(
            object : UiGraphArguments {},
        )

        // TODO: Replace with withAppTestDependencies when runComposeUiTest allows providing a suspend fun
        runAppTest(
            context = appTestContext,
            timeout = timeout,
        ) {
            // Let any background jobs launch and stabilize before running the test body
            advanceUntilIdle()
            testBody(
                this@runComposeUiTest,
                uiGraph,
            )
        }
    }

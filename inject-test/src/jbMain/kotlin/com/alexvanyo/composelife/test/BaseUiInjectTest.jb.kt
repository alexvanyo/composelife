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
import kotlinx.coroutines.test.TestResult
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

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
}

@OptIn(ExperimentalTestApi::class)
expect fun BaseUiInjectTest.runUiTest(
    appTestContext: CoroutineContext = EmptyCoroutineContext,
    timeout: Duration = 60.seconds,
    testBody: suspend ComposeUiTest.(uiGraph: UiGraph) -> Unit,
): TestResult

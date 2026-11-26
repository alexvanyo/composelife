/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.settings

import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.test.BaseInjectTestCtx
import com.alexvanyo.composelife.test.BaseUiInjectTestCtx
import com.alexvanyo.composelife.tracing.TestTraceDriver
import com.alexvanyo.composelife.tracing.Tracer
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.GraphExtension
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.createGraphFactory

@DependencyGraph(AppScope::class)
interface TestApplicationGraph :
    ApplicationGraph,
    BaseInjectTestCtx,
    TestUiGraph.Factory {
    @DependencyGraph.Factory
    fun interface Factory {
        fun create(
            @Provides tracer: Tracer,
            @Provides applicationGraphArguments: ApplicationGraphArguments,
        ): TestApplicationGraph
    }
}

@GraphExtension(UiScope::class)
interface TestUiGraph :
    UiGraph,
    BaseUiInjectTestCtx,
    InlineSettingsPaneTestsCtx {
    @GraphExtension.Factory
    fun interface Factory {
        fun create(@Provides uiGraphArguments: UiGraphArguments): TestUiGraph
    }
}

private val testTraceDriver = TestTraceDriver()
internal fun createTestApplicationGraph(applicationGraphArguments: ApplicationGraphArguments): TestApplicationGraph =
    createGraphFactory<TestApplicationGraph.Factory>().create(
        tracer = testTraceDriver.tracer,
        applicationGraphArguments = applicationGraphArguments,
    )

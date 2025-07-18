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

package com.alexvanyo.composelife.ui.cells

import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.model.di.CellStateParserModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.ApplicationComponentArguments
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.Provides

@DependencyGraph(AppScope::class, isExtendable = true)
interface TestComposeLifeApplicationComponent : ApplicationComponent {
    @DependencyGraph.Factory
    fun interface Factory {
        fun create(
            @Provides applicationComponentArguments: ApplicationComponentArguments,
        ): TestComposeLifeApplicationComponent
    }
}

@ContributesTo(AppScope::class)
interface TestComposeLifeApplicationEntryPoint :
    UpdatableModule,
    CellStateParserModule,
    TestDispatcherModule

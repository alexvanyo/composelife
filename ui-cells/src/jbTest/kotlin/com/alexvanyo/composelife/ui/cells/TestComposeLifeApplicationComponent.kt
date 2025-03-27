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
import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.model.di.CellStateParserModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import software.amazon.lastmile.kotlin.inject.anvil.AppScope

expect abstract class TestComposeLifeApplicationComponent : ApplicationComponent<TestComposeLifeApplicationEntryPoint> {

    abstract override val entryPoint: TestComposeLifeApplicationEntryPoint

    companion object
}

@EntryPoint(AppScope::class)
interface TestComposeLifeApplicationEntryPoint :
    UpdatableModule,
    CellStateParserModule,
    TestDispatcherModule {
    val uiComponentFactory: TestComposeLifeUiComponent.Factory
}

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

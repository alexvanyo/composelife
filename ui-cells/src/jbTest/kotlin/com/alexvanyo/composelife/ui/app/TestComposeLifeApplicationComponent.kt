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

package com.alexvanyo.composelife.ui.app

import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.model.di.CellStateParserModule
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.preferences.di.TestPreferencesComponent
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule

expect abstract class TestComposeLifeApplicationComponent :
    ApplicationComponent<TestComposeLifeApplicationEntryPoint>,
    TestDispatchersComponent,
    TestPreferencesComponent,
    UpdatableModule,
    CellStateParserModule {

    override val entryPoint: TestComposeLifeApplicationEntryPoint

    companion object
}

interface TestComposeLifeApplicationEntryPoint :
    DispatchersModule,
    PreferencesModule,
    UpdatableModule,
    CellStateParserModule

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

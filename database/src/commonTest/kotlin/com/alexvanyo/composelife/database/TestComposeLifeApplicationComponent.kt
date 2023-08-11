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

package com.alexvanyo.composelife.database

import com.alexvanyo.composelife.database.di.DatabaseModule
import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule

expect abstract class TestComposeLifeApplicationComponent :
    ApplicationComponent<TestComposeLifeApplicationEntryPoint>,
    TestDatabaseComponent,
    TestDispatchersComponent,
    UpdatableModule {
    companion object
}

interface TestComposeLifeApplicationEntryPoint :
    DatabaseModule,
    DispatchersModule

expect fun TestComposeLifeApplicationComponent.Companion.create(): TestComposeLifeApplicationComponent

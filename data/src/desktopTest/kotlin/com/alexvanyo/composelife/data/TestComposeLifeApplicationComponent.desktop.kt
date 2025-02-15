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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.di.RepositoryComponent
import com.alexvanyo.composelife.data.di.RepositoryModule
import com.alexvanyo.composelife.database.di.DatabaseModule
import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.MergeComponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@MergeComponent(AppScope::class)
@SingleIn(AppScope::class)
actual abstract class TestComposeLifeApplicationComponent :
    ApplicationComponent<TestComposeLifeApplicationEntryPoint>(),
    RepositoryComponent,
    TestDatabaseComponent,
    DispatchersModule,
    TestDispatcherModule,
    UpdatableModule {

    actual override val entryPoint: TestComposeLifeApplicationEntryPoint get() =
        object :
            TestComposeLifeApplicationEntryPoint,
            RepositoryModule by this,
            DatabaseModule by this,
            DispatchersModule by this,
            UpdatableModule by this {}

    actual companion object
}

actual fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent =
    TestComposeLifeApplicationComponent::class.create()

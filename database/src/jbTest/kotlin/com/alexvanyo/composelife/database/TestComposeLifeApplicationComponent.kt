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
import com.alexvanyo.composelife.database.di.QueriesModule
import com.alexvanyo.composelife.dispatchers.CellTickerTestDispatcher
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.test.TestDispatcher
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

expect abstract class TestComposeLifeApplicationComponent : ApplicationComponent<TestComposeLifeApplicationEntryPoint> {

    abstract override val entryPoint: TestComposeLifeApplicationEntryPoint

    companion object
}

@SingleIn(AppScope::class)
@Inject
class TestComposeLifeApplicationEntryPoint(
    override val composeLifeDatabase: ComposeLifeDatabase,
    override val dispatchers: ComposeLifeDispatchers,
    override val updatables: Set<Updatable>,
    override val generalTestDispatcher: @GeneralTestDispatcher TestDispatcher,
    override val cellTickerTestDispatcher: @CellTickerTestDispatcher TestDispatcher,
    override val cellStateQueries: CellStateQueries
) : DatabaseModule,
    DispatchersModule,
    TestDispatcherModule,
    QueriesModule,
    UpdatableModule

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

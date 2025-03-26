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

package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.database.CellStateQueries
import com.alexvanyo.composelife.database.PatternCollectionQueries
import com.alexvanyo.composelife.dispatchers.CellTickerTestDispatcher
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.network.FakeRequestHandler
import com.alexvanyo.composelife.scopes.ApplicationComponent
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
    val cellStateRepository: CellStateRepository,
    val cellStateQueries: CellStateQueries,
    val patternCollectionRepository: PatternCollectionRepository,
    val patternCollectionQueries: PatternCollectionQueries,
    val dispatchers: ComposeLifeDispatchers,
    override val updatables: Set<Updatable>,
    val generalTestDispatcher: @GeneralTestDispatcher TestDispatcher,
    val cellTickerTestDispatcher: @CellTickerTestDispatcher TestDispatcher,
    val fakeRequestHandler: FakeRequestHandler,
) : UpdatableModule

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

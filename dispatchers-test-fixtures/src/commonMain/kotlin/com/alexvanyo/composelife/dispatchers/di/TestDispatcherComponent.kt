/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.dispatchers.di

import com.alexvanyo.composelife.clock.di.ClockComponent
import com.alexvanyo.composelife.dispatchers.CellTickerTestDispatcher
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.dispatchers.clock
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.TestDispatcher
import kotlin.time.Clock
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@ContributesTo(AppScope::class, replaces = [ClockComponent::class])
interface TestDispatcherComponent {

    @Provides
    @SingleIn(AppScope::class)
    @GeneralTestDispatcher
    fun providesGeneralTestCoroutineScheduler(): TestCoroutineScheduler =
        TestCoroutineScheduler()

    @Provides
    @SingleIn(AppScope::class)
    @GeneralTestDispatcher
    fun providesGeneralTestDispatcher(
        testCoroutineScheduler: @GeneralTestDispatcher TestCoroutineScheduler,
    ): TestDispatcher =
        StandardTestDispatcher(
            scheduler = testCoroutineScheduler,
        )

    @Provides
    fun providesClock(
        testCoroutineScheduler: @GeneralTestDispatcher TestCoroutineScheduler,
    ): Clock = testCoroutineScheduler.clock

    @Provides
    @SingleIn(AppScope::class)
    @CellTickerTestDispatcher
    fun providesCellTickerTestDispatcher(): TestDispatcher =
        StandardTestDispatcher()
}

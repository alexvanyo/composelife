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

package com.alexvanyo.composelife

import android.app.Application
import com.alexvanyo.composelife.algorithm.di.AlgorithmComponent
import com.alexvanyo.composelife.algorithm.di.AlgorithmModule
import com.alexvanyo.composelife.clock.di.ClockModule
import com.alexvanyo.composelife.data.di.RepositoryComponent
import com.alexvanyo.composelife.data.di.RepositoryModule
import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.donotkeepprocess.di.DoNotKeepProcessComponent
import com.alexvanyo.composelife.filesystem.di.TestFileSystemComponent
import com.alexvanyo.composelife.imageloader.di.ImageLoaderComponent
import com.alexvanyo.composelife.imageloader.di.ImageLoaderModule
import com.alexvanyo.composelife.model.di.CellStateParserModule
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.preferences.di.TestPreferencesComponent
import com.alexvanyo.composelife.processlifecycle.di.ProcessLifecycleComponent
import com.alexvanyo.composelife.random.di.RandomComponent
import com.alexvanyo.composelife.random.di.RandomModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.ui.cells.di.CellsImageLoadingComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.MergeComponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@MergeComponent(AppScope::class)
@SingleIn(AppScope::class)
abstract class TestComposeLifeApplicationComponent(
    application: Application,
) : ApplicationComponent<TestComposeLifeApplicationEntryPoint>(application),
    AlgorithmComponent,
    RepositoryComponent,
    TestDatabaseComponent,
    TestDispatchersComponent,
    TestPreferencesComponent,
    RandomComponent,
    ClockModule,
    ProcessLifecycleComponent,
    DoNotKeepProcessComponent,
    ImageLoaderComponent,
    CellsImageLoadingComponent,
    TestFileSystemComponent,
    UpdatableModule,
    CellStateParserModule {

    override val entryPoint: TestComposeLifeApplicationEntryPoint get() =
        object :
            TestComposeLifeApplicationEntryPoint,
            RandomModule by this,
            ClockModule by this,
            RepositoryModule by this,
            AlgorithmModule by this,
            DispatchersModule by this,
            PreferencesModule by this,
            UpdatableModule by this,
            CellStateParserModule by this,
            ImageLoaderModule by this {}

    companion object
}

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

interface TestComposeLifeApplicationEntryPoint :
    RandomModule,
    ClockModule,
    RepositoryModule,
    AlgorithmModule,
    DispatchersModule,
    PreferencesModule,
    UpdatableModule,
    CellStateParserModule,
    ImageLoaderModule

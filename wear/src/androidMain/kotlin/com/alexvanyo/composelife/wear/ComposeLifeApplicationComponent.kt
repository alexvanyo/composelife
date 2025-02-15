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

package com.alexvanyo.composelife.wear

import android.app.Application
import androidx.lifecycle.LifecycleOwner
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.di.AlgorithmModule
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.processlifecycle.ProcessLifecycleOwner
import com.alexvanyo.composelife.processlifecycle.di.ProcessLifecycleModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.MergeComponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@MergeComponent(AppScope::class)
@SingleIn(AppScope::class)
abstract class ComposeLifeApplicationComponent(
    application: Application,
) : ApplicationComponent<ComposeLifeApplicationEntryPoint>(application) {

    abstract override val entryPoint: ComposeLifeApplicationEntryPoint

    companion object
}

@SingleIn(AppScope::class)
@Inject
class ComposeLifeApplicationEntryPoint(
    override val updatables: Set<Updatable>,
    override val processLifecycleOwner: @ProcessLifecycleOwner LifecycleOwner,
    override val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    override val dispatchers: ComposeLifeDispatchers,
    val uiComponentFactory: ComposeLifeUiComponent.Factory,
) : UpdatableModule,
    ProcessLifecycleModule,
    AlgorithmModule,
    DispatchersModule

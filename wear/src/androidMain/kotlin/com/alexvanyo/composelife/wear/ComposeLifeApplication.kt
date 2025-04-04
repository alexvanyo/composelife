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

package com.alexvanyo.composelife.wear

import android.app.Application
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.lifecycleScope
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.algorithm.di.AlgorithmModule
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.processlifecycle.di.ProcessLifecycleModule
import com.alexvanyo.composelife.scopes.ApplicationComponentOwner
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.strictmode.initStrictModeIfNeeded
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope
import software.amazon.lastmile.kotlin.inject.anvil.AppScope

@EntryPoint(AppScope::class)
interface ComposeLifeApplicationEntryPoint : UpdatableModule,
    ProcessLifecycleModule,
    AlgorithmModule,
    DispatchersModule {
    val uiComponentFactory: ComposeLifeUiComponent.Factory
}


class ComposeLifeApplication : Application(), ApplicationComponentOwner {

    override lateinit var applicationComponent: ComposeLifeApplicationComponent

    private val entryPoint get() = applicationComponent.getEntryPoint<ComposeLifeApplicationEntryPoint>()

    override val uiComponentFactory: (UiComponentArguments) -> ComposeLifeUiComponent =
        { entryPoint.uiComponentFactory.createComponent(it.activity) }

    override fun onCreate() {
        super.onCreate()

        initStrictModeIfNeeded()

        applicationComponent = ComposeLifeApplicationComponent::class.create(this)

        val processLifecycleOwner = entryPoint.processLifecycleOwner
        val updatables = entryPoint.updatables

        // Update all singleton scoped updatables in the process lifecycle scope, when its created.
        // Effectively, this is just a permanently running coroutine scope.
        processLifecycleOwner.lifecycleScope.launch {
            processLifecycleOwner.repeatOnLifecycle(Lifecycle.State.CREATED) {
                supervisorScope {
                    updatables.forEach { updatable ->
                        launch {
                            updatable.update()
                        }
                    }
                }
            }
        }
    }
}

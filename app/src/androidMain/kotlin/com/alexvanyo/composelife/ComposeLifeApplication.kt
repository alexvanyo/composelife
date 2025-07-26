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

package com.alexvanyo.composelife

import android.app.Application
import android.content.Context
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.lifecycleScope
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.processlifecycle.ProcessLifecycleOwner
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.scopes.ApplicationGraphOwner
import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.strictmode.initStrictModeIfNeeded
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.asContribution
import dev.zacsweers.metro.createGraph
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope

@ContributesTo(AppScope::class)
interface ComposeLifeApplicationEntryPoint {
    @ProcessLifecycleOwner val processLifecycleOwner: LifecycleOwner
    val updatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val ApplicationGraph.composeLifeApplicationEntryPoint: ComposeLifeApplicationEntryPoint get() =
    this as ComposeLifeApplicationEntryPoint

class ComposeLifeApplication : Application(), ApplicationGraphOwner {

    override lateinit var applicationGraph: ApplicationGraph

    override fun onCreate() {
        super.onCreate()

        initStrictModeIfNeeded()

        val globalGraph = createGraph<GlobalGraph>()
        applicationGraph = globalGraph.asContribution<ApplicationGraph.Factory>().create(
            object : ApplicationGraphArguments {
                override val applicationContext: Context = this@ComposeLifeApplication
            },
        )
        val entryPoint = applicationGraph.composeLifeApplicationEntryPoint
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

@DependencyGraph(GlobalScope::class, isExtendable = true)
interface GlobalGraph

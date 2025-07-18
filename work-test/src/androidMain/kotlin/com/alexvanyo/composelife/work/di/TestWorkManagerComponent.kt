/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.work.di

import android.content.Context
import androidx.work.ListenableWorker
import androidx.work.WorkManager
import androidx.work.testing.SynchronousExecutor
import androidx.work.testing.WorkManagerTestInitHelper
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.work.AssistedWorkerFactory
import com.alexvanyo.composelife.work.InjectWorkerFactory
import kotlinx.coroutines.awaitCancellation
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.SingleIn
import kotlin.reflect.KClass

@ContributesTo(AppScope::class, replaces = [WorkManagerComponent::class])
interface TestWorkManagerComponent {

    val workerFactoryMap: Map<String, AssistedWorkerFactory>

    @Provides
    fun providesWorkerFactoryClassNameMap(
        workerFactoryClassMap: Map<KClass<out ListenableWorker>, AssistedWorkerFactory>
    ): Map<String, AssistedWorkerFactory> =
        workerFactoryClassMap.mapKeys { it.key.java.name }

    @Provides
    fun providesWorkManagerConfiguration(
        injectWorkerFactory: InjectWorkerFactory,
    ): androidx.work.Configuration =
        androidx.work.Configuration.Builder()
            .setWorkerFactory(injectWorkerFactory)
            .setExecutor(SynchronousExecutor())
            .setTaskExecutor(SynchronousExecutor())
            .build()

    @Provides
    @SingleIn(AppScope::class)
    fun providesWorkManager(
        @ApplicationContext context: Context,
        workManagerConfiguration: androidx.work.Configuration
    ): WorkManager {
        WorkManagerTestInitHelper.initializeTestWorkManager(
            context,
            workManagerConfiguration,
            WorkManagerTestInitHelper.ExecutorsMode.PRESERVE_EXECUTORS,
        )
        return WorkManager.getInstance(context)
    }

    @Provides
    @SingleIn(AppScope::class)
    @IntoSet
    fun providesWorkManagerIntoUpdatable(): Updatable =
        object : Updatable {
            override suspend fun update(): Nothing =
                try {
                    awaitCancellation()
                } finally {
                    WorkManagerTestInitHelper.closeWorkDatabase()
                }
        }
}

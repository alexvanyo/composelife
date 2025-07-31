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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.database.di

import app.cash.sqldelight.db.SqlDriver
import app.cash.sqldelight.db.use
import app.cash.sqldelight.driver.worker.createDefaultWebWorkerDriver
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.updatable.AppUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.awaitCancellation

@ContributesTo(AppScope::class)
@BindingContainer
interface DriverBindings {

    companion object {
        @Provides
        @SingleIn(AppScope::class)
        internal fun providesDriver(): SqlDriver =
            createDefaultWebWorkerDriver().also(ComposeLifeDatabase.Schema::create)

        @Provides
        @SingleIn(AppScope::class)
        @IntoSet
        @AppUpdatable
        internal fun providesDriverClosingIntoUpdatable(
            driver: SqlDriver,
        ): Updatable = object : Updatable {
            override suspend fun update(): Nothing =
                driver.use { _ ->
                    awaitCancellation()
                }
        }
    }
}

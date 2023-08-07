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

package com.alexvanyo.composelife.database.di

import app.cash.sqldelight.db.SqlDriver
import app.cash.sqldelight.driver.jdbc.sqlite.JdbcSqliteDriver
import com.alexvanyo.composelife.scopes.Singleton
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.awaitCancellation
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides

actual interface DriverComponent : UpdatableModule {

    @Provides
    @Singleton
    fun providesDriver(): SqlDriver =
        JdbcSqliteDriver(JdbcSqliteDriver.IN_MEMORY)

    @Provides
    @Singleton
    @IntoSet
    fun providesDriverClosingIntoUpdatable(
        driver: SqlDriver,
    ): Updatable = object : Updatable {
        override suspend fun update(): Nothing =
            driver.use { _ ->
                awaitCancellation()
            }
    }
}

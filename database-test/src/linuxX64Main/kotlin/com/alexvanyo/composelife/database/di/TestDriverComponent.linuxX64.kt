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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.database.di

import app.cash.sqldelight.db.SqlDriver
import app.cash.sqldelight.db.use
import app.cash.sqldelight.driver.native.NativeSqliteDriver
import app.cash.sqldelight.driver.native.wrapConnection
import co.touchlab.sqliter.DatabaseConfiguration
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.scopes.Singleton
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides

actual interface TestDriverComponent {

    @Provides
    @SingleIn(AppScope::class)
    fun providesDriver(): SqlDriver {
        val schema = ComposeLifeDatabase.Schema
        return NativeSqliteDriver(
            configuration = DatabaseConfiguration(
                name = "test.db",
                version = if (schema.version > Int.MAX_VALUE) {
                    error("Schema version is larger than Int.MAX_VALUE: ${schema.version}.")
                } else {
                    schema.version.toInt()
                },
                create = { connection -> wrapConnection(connection) { schema.create(it) } },
                upgrade = { connection, oldVersion, newVersion ->
                    wrapConnection(connection) {
                        schema.migrate(
                            it,
                            oldVersion.toLong(),
                            newVersion.toLong(),
                        )
                    }
                },
            ),
        )
    }

    @Provides
    @SingleIn(AppScope::class)
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

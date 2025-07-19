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

import android.content.Context
import androidx.sqlite.db.SupportSQLiteDatabase
import app.cash.sqldelight.async.coroutines.synchronous
import app.cash.sqldelight.db.SqlDriver
import app.cash.sqldelight.driver.android.AndroidSqliteDriver
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.SingleIn

@ContributesTo(AppScope::class, replaces = [DriverComponent::class])
interface TestDriverComponent {

    @Provides
    @SingleIn(AppScope::class)
    fun providesDriver(
        @ApplicationContext context: Context,
    ): SqlDriver {
        val schema = ComposeLifeDatabase.Schema.synchronous()
        return AndroidSqliteDriver(
            schema = schema,
            context = context,
            name = null,
            callback = object : AndroidSqliteDriver.Callback(schema) {
                override fun onConfigure(db: SupportSQLiteDatabase) {
                    db.setForeignKeyConstraintsEnabled(true)
                }
            },
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

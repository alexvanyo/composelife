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

package com.alexvanyo.composelife.database

import android.content.Context
import androidx.sqlite.db.SupportSQLiteDatabase
import app.cash.sqldelight.async.coroutines.synchronous
import app.cash.sqldelight.driver.android.AndroidSqliteDriver
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.awaitCancellation

@ContributesTo(AppScope::class, replaces = [AndroidComposeLifeDriverBindings::class])
@BindingContainer
interface AndroidComposeLifeTestDriverBindings {

    @Binds
    val AndroidComposeLifeTestDriver.bind: ComposeLifeDriver

    @Binds
    @IntoSet
    @ForScope(AppScope::class)
    val AndroidComposeLifeTestDriver.bindIntoUpdatable: Updatable
}

@SingleIn(AppScope::class)
@Inject
class AndroidComposeLifeTestDriver(
    @ApplicationContext context: Context,
) : ComposeLifeDriver, Updatable {

    private val schema = ComposeLifeDatabase.Schema.synchronous()
    override val sqlDriver = AndroidSqliteDriver(
        schema = schema,
        context = context,
        name = null,
        callback = object : AndroidSqliteDriver.Callback(schema) {
            override fun onConfigure(db: SupportSQLiteDatabase) {
                db.setForeignKeyConstraintsEnabled(true)
            }
        },
    )

    override suspend fun awaitDriverReady() = Unit

    override suspend fun update(): Nothing =
        sqlDriver.use {
            awaitCancellation()
        }
}

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

import androidx.sqlite.driver.bundled.BundledSQLiteDriver
import app.cash.sqldelight.db.SqlDriver
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.updatable.Updatable
import com.eygraber.sqldelight.androidx.driver.AndroidxSqliteConcurrencyModel
import com.eygraber.sqldelight.androidx.driver.AndroidxSqliteConfiguration
import com.eygraber.sqldelight.androidx.driver.AndroidxSqliteDatabaseType
import com.eygraber.sqldelight.androidx.driver.AndroidxSqliteDriver
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.awaitCancellation

@ContributesTo(AppScope::class)
@BindingContainer
interface DesktopComposeLifeDriverBindings {

    @Binds
    val DesktopComposeLifeDriver.bind: ComposeLifeDriver

    @Binds
    @IntoSet
    @ForScope(AppScope::class)
    val DesktopComposeLifeDriver.bindIntoUpdatable: Updatable
}

@SingleIn(AppScope::class)
@Inject
class DesktopComposeLifeDriver(
    dispatchers: ComposeLifeDispatchers,
) : ComposeLifeDriver, Updatable {

    override val sqlDriver: SqlDriver = AndroidxSqliteDriver(
        driver = BundledSQLiteDriver(),
        databaseType = AndroidxSqliteDatabaseType.Memory,
        schema = ComposeLifeDatabase.Schema,
        configuration = AndroidxSqliteConfiguration(
            concurrencyModel = AndroidxSqliteConcurrencyModel.MultipleReadersSingleWriter(
                isWal = true,
                dispatcherProvider = { parallelism, _ -> dispatchers.IOWithLimitedParallelism(parallelism) },
            ),
        ),
        onConfigure = {
            setForeignKeyConstraintsEnabled(true)
        },
    )

    override suspend fun awaitDriverReady() = Unit

    override suspend fun update(): Nothing =
        sqlDriver.use {
            awaitCancellation()
        }
}

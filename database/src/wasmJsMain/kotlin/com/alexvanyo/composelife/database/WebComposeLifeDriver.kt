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

import app.cash.sqldelight.async.coroutines.awaitCreate
import app.cash.sqldelight.db.SqlDriver
import app.cash.sqldelight.db.use
import app.cash.sqldelight.driver.worker.createDefaultWebWorkerDriver
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.awaitCancellation

@ContributesTo(AppScope::class)
@BindingContainer
interface WebComposeLifeDriverBindings {

    @Binds
    val WebComposeLifeDriver.bind: ComposeLifeDriver

    @Binds
    @IntoSet
    @ForScope(AppScope::class)
    val WebComposeLifeDriver.bindIntoUpdatable: Updatable
}

@SingleIn(AppScope::class)
@Inject
class WebComposeLifeDriver : ComposeLifeDriver, Updatable {
    override val sqlDriver: SqlDriver = createDefaultWebWorkerDriver()

    private val driverReadyDeferred = CompletableDeferred<Unit>()

    override suspend fun awaitDriverReady() = driverReadyDeferred.await()

    override suspend fun update(): Nothing =
        sqlDriver.use {
            ComposeLifeDatabase.Schema.awaitCreate(it)
            driverReadyDeferred.complete(Unit)
            awaitCancellation()
        }
}

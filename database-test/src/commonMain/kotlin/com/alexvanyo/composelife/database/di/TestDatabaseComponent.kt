/*
 * Copyright 2023 The Android Open Source Project
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
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.database.PatternCollection
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@ContributesTo(AppScope::class, replaces = [DatabaseComponent::class])
interface TestDatabaseComponent {

    @Provides
    @SingleIn(AppScope::class)
    fun providesDatabase(
        driver: SqlDriver,
        cellStateAdapter: CellState.Adapter,
        patternCollectionAdapter: PatternCollection.Adapter,
    ): ComposeLifeDatabase =
        ComposeLifeDatabase(
            driver = driver,
            cellStateAdapter = cellStateAdapter,
            patternCollectionAdapter = patternCollectionAdapter,
        )
}

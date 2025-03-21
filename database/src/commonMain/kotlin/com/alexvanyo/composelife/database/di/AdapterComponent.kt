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

import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateIdAdapter
import com.alexvanyo.composelife.database.InstantAdapter
import com.alexvanyo.composelife.database.PatternCollection
import com.alexvanyo.composelife.database.PatternCollectionIdAdapter
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo

@ContributesTo(AppScope::class)
interface AdapterComponent {

    @Provides
    fun providesCellStateAdapter(
        cellStateIdAdapter: CellStateIdAdapter,
    ): CellState.Adapter =
        CellState.Adapter(
            idAdapter = cellStateIdAdapter,
        )

    @Provides
    fun providesPatternCollectionAdapter(
        patternCollectionIdAdapter: PatternCollectionIdAdapter,
        instantAdapter: InstantAdapter,
    ): PatternCollection.Adapter =
        PatternCollection.Adapter(
            idAdapter = patternCollectionIdAdapter,
            lastSuccessfulSynchronizationTimestampAdapter = instantAdapter,
        )
}

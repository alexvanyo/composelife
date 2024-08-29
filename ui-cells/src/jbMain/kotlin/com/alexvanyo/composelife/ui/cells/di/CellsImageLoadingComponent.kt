/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.cells.di

import com.alexvanyo.composelife.imageloader.di.FetcherFactoryWithType
import com.alexvanyo.composelife.imageloader.di.KeyerWithType
import com.alexvanyo.composelife.imageloader.di.withType
import com.alexvanyo.composelife.scopes.Singleton
import com.alexvanyo.composelife.ui.cells.CellsFetcher
import com.alexvanyo.composelife.ui.cells.CellsKeyer
import me.tatarka.inject.annotations.IntoSet
import me.tatarka.inject.annotations.Provides

interface CellsImageLoadingComponent {

    @Provides
    @Singleton
    @IntoSet
    fun providesCellsFetcherFactoryIntoFetcherFactories(
        cellsFetcherFactory: CellsFetcher.Factory,
    ): FetcherFactoryWithType<out Any> = cellsFetcherFactory.withType()

    @Provides
    @Singleton
    @IntoSet
    fun providesCellsKeyerIntoKeyers(
        cellsKeyer: CellsKeyer,
    ): KeyerWithType<out Any> = cellsKeyer.withType()
}
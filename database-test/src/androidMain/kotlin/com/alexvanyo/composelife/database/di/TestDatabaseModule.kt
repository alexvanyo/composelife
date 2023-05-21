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

import android.content.Context
import androidx.room.Room
import com.alexvanyo.composelife.database.AppDatabase
import com.alexvanyo.composelife.updatable.Updatable
import dagger.Module
import dagger.Provides
import dagger.hilt.android.qualifiers.ApplicationContext
import dagger.hilt.components.SingletonComponent
import dagger.hilt.testing.TestInstallIn
import dagger.multibindings.IntoSet
import kotlinx.coroutines.asExecutor
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.test.TestDispatcher
import javax.inject.Singleton

@Module
@TestInstallIn(
    components = [SingletonComponent::class],
    replaces = [DatabaseModule::class],
)
interface TestDatabaseModule {

    companion object {

        @Provides
        @Singleton
        @IntoSet
        fun providesDatabaseClosingIntoUpdatable(
            appDatabase: AppDatabase,
        ): Updatable = object : Updatable {
            override suspend fun update(): Nothing =
                try {
                    awaitCancellation()
                } finally {
                    appDatabase.close()
                }
        }

        @Provides
        @Singleton
        fun providesDatabase(
            testDispatcher: TestDispatcher,
            @ApplicationContext context: Context,
        ): AppDatabase =
            Room.inMemoryDatabaseBuilder(
                context = context,
                klass = AppDatabase::class.java,
            )
                .allowMainThreadQueries()
                .setTransactionExecutor(testDispatcher.asExecutor())
                .setQueryExecutor(testDispatcher.asExecutor())
                .build()
    }
}

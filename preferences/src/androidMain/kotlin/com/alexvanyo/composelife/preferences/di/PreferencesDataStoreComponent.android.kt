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

package com.alexvanyo.composelife.preferences.di

import androidx.datastore.dataStoreFile
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.DiskPreferencesDataStore
import com.alexvanyo.composelife.preferences.PreferencesCoroutineScope
import com.alexvanyo.composelife.preferences.PreferencesDataStore
import com.alexvanyo.composelife.preferences.PreferencesProtoPath
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.scopes.Singleton
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import me.tatarka.inject.annotations.Provides
import okio.Path.Companion.toOkioPath

actual interface PreferencesDataStoreComponent :
    PreferencesDataStoreModule,
    PreferencesFileSystemComponent {

    val DiskPreferencesDataStore.bind: PreferencesDataStore
        @Provides get() = this

    @Provides
    fun providesDataStorePath(
        context: ApplicationContext,
    ): PreferencesProtoPath = context.dataStoreFile("preferences.pb").absoluteFile.toOkioPath()

    @Provides
    @Singleton
    @Suppress("InjectDispatcher") // Dispatchers are injected via dispatchers
    fun providesPreferencesCoroutineScope(
        dispatchers: ComposeLifeDispatchers,
    ): PreferencesCoroutineScope = CoroutineScope(
        dispatchers.IO + SupervisorJob(),
    )
}

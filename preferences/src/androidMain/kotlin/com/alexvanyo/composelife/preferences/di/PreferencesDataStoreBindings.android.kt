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

import android.content.Context
import androidx.datastore.dataStoreFile
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.PreferencesCoroutineScope
import com.alexvanyo.composelife.preferences.PreferencesProtoPath
import com.alexvanyo.composelife.scopes.ApplicationContext
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.SupervisorJob
import dev.zacsweers.metro.Provides
import okio.Path
import okio.Path.Companion.toOkioPath
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.SingleIn

@ContributesTo(AppScope::class)
@BindingContainer
interface PreferencesDataStoreBindings {
    companion object {
        @Provides
        @PreferencesProtoPath
        fun providesDataStorePath(
            @ApplicationContext context: Context,
        ): Path = context.dataStoreFile("preferences.pb").absoluteFile.toOkioPath()

        @Provides
        @SingleIn(AppScope::class)
        @PreferencesCoroutineScope
        fun providesPreferencesCoroutineScope(
            dispatchers: ComposeLifeDispatchers,
        ): CoroutineScope = CoroutineScope(
            dispatchers.IO + SupervisorJob(),
        )
    }
}

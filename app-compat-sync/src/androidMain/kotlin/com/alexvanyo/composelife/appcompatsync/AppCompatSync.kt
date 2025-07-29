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

package com.alexvanyo.composelife.appcompatsync

import android.app.UiModeManager
import android.content.Context
import android.os.Build
import androidx.appcompat.app.AppCompatDelegate
import androidx.compose.runtime.snapshotFlow
import androidx.core.content.getSystemService
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.darkThemeConfigState
import com.alexvanyo.composelife.resourcestate.successes
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.updatable.AppUpdatable
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach

@ContributesTo(AppScope::class)
@BindingContainer
interface AppCompatSyncBindings {
    @Binds
    @IntoSet
    @AppUpdatable
    val AppCompatSync.bindIntoUpdatable: Updatable
}

@Inject
@SingleIn(AppScope::class)
class AppCompatSync(
    private val composeLifePreferences: ComposeLifePreferences,
    @ApplicationContext context: Context,
) : Updatable {
    private val uiModeManager = context.getSystemService<UiModeManager>()

    override suspend fun update(): Nothing {
        snapshotFlow {
            composeLifePreferences.darkThemeConfigState
        }
            .successes()
            .onEach { darkThemeConfig ->
                // If we can, update and persist the application-defined night mode
                if (Build.VERSION.SDK_INT >= 31) {
                    uiModeManager?.setApplicationNightMode(darkThemeConfig.value.uiModeManagerMode)
                } else {
                    AppCompatDelegate.setDefaultNightMode(darkThemeConfig.value.appCompatDelegateMode)
                }
            }
            .collect()

        error("snapshotFlow can not complete normally")
    }
}

internal val DarkThemeConfig.uiModeManagerMode get() =
    when (this) {
        DarkThemeConfig.Dark -> UiModeManager.MODE_NIGHT_YES
        DarkThemeConfig.FollowSystem -> UiModeManager.MODE_NIGHT_AUTO
        DarkThemeConfig.Light -> UiModeManager.MODE_NIGHT_NO
    }

internal val DarkThemeConfig.appCompatDelegateMode get() =
    when (this) {
        DarkThemeConfig.Dark -> AppCompatDelegate.MODE_NIGHT_YES
        DarkThemeConfig.FollowSystem -> AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM
        DarkThemeConfig.Light -> AppCompatDelegate.MODE_NIGHT_NO
    }

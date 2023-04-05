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
import com.alexvanyo.composelife.resourcestate.successes
import com.alexvanyo.composelife.updatable.Updatable
import dagger.hilt.android.qualifiers.ApplicationContext
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import javax.inject.Inject

class AppCompatSync @Inject constructor(
    private val composeLifePreferences: ComposeLifePreferences,
    @ApplicationContext private val context: Context,
) : Updatable {
    private val uiModeManager = context.getSystemService<UiModeManager>()

    override suspend fun update(): Nothing {
        snapshotFlow {
            composeLifePreferences.darkThemeConfigState
        }
            .successes()
            .onEach { darkThemeConfig ->
                AppCompatDelegate.setDefaultNightMode(
                    when (darkThemeConfig.value) {
                        DarkThemeConfig.Dark -> AppCompatDelegate.MODE_NIGHT_YES
                        DarkThemeConfig.FollowSystem -> AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM
                        DarkThemeConfig.Light -> AppCompatDelegate.MODE_NIGHT_NO
                    },
                )
                // If we can, update and persist the application-defined night mode
                if (Build.VERSION.SDK_INT >= 31) {
                    uiModeManager?.setApplicationNightMode(
                        when (darkThemeConfig.value) {
                            DarkThemeConfig.Dark -> UiModeManager.MODE_NIGHT_YES
                            DarkThemeConfig.FollowSystem -> UiModeManager.MODE_NIGHT_AUTO
                            DarkThemeConfig.Light -> UiModeManager.MODE_NIGHT_NO
                        },
                    )
                }
            }
            .collect()

        error("snapshotFlow can not complete normally")
    }
}

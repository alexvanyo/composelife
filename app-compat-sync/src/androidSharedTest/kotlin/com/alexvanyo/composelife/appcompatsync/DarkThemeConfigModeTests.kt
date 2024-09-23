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

package com.alexvanyo.composelife.appcompatsync

import android.app.UiModeManager
import androidx.appcompat.app.AppCompatDelegate
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import kotlin.test.Test
import kotlin.test.assertEquals

class DarkThemeConfigModeTests {

    @Test
    fun dark_theme_config_light_to_ui_mode_manager_mode_converts_correctly() {
        assertEquals(
            UiModeManager.MODE_NIGHT_NO,
            DarkThemeConfig.Light.uiModeManagerMode,
        )
    }

    @Test
    fun dark_theme_config_dark_to_ui_mode_manager_mode_converts_correctly() {
        assertEquals(
            UiModeManager.MODE_NIGHT_YES,
            DarkThemeConfig.Dark.uiModeManagerMode,
        )
    }

    @Test
    fun dark_theme_config_follow_system_to_ui_mode_manager_mode_converts_correctly() {
        assertEquals(
            UiModeManager.MODE_NIGHT_AUTO,
            DarkThemeConfig.FollowSystem.uiModeManagerMode,
        )
    }

    @Test
    fun dark_theme_config_light_to_app_compat_delegate_mode_converts_correctly() {
        assertEquals(
            AppCompatDelegate.MODE_NIGHT_NO,
            DarkThemeConfig.Light.appCompatDelegateMode,
        )
    }

    @Test
    fun dark_theme_config_dark_to_app_compat_delegate_mode_converts_correctly() {
        assertEquals(
            AppCompatDelegate.MODE_NIGHT_YES,
            DarkThemeConfig.Dark.appCompatDelegateMode,
        )
    }

    @Test
    fun dark_theme_config_follow_system_to_app_compat_delegate_mode_converts_correctly() {
        assertEquals(
            AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM,
            DarkThemeConfig.FollowSystem.appCompatDelegateMode,
        )
    }
}

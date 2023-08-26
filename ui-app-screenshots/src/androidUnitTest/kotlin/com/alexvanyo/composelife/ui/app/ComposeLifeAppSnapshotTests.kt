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

package com.alexvanyo.composelife.ui.app

import com.alexvanyo.composelife.ui.app.util.BaseRoborazziTest
import kotlin.test.Test

class ComposeLifeAppSnapshotTests(
    deviceName: String,
    deviceQualifiers: String,
    darkTheme: Boolean,
    fontScale: Float,
) : BaseRoborazziTest(deviceName, deviceQualifiers, darkTheme, fontScale) {

    @Test
    fun loading_preferences_compose_life_app_preview() {
        snapshot {
            LoadingPreferencesComposeLifeAppPreview()
        }
    }

    @Test
    fun loading_cell_state_compose_life_app_preview() {
        snapshot {
            LoadingCellStateComposeLifeAppPreview()
        }
    }

    @Test
    fun loaded_compose_life_app_preview() {
        snapshot {
            LoadedComposeLifeAppPreview()
        }
    }
}

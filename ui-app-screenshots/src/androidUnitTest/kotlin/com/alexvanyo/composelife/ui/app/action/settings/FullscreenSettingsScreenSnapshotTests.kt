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

package com.alexvanyo.composelife.ui.app.action.settings

import com.alexvanyo.composelife.ui.app.util.BasePaparazziTest
import kotlin.test.Test

class FullscreenSettingsScreenSnapshotTests : BasePaparazziTest() {

    @Test
    fun fullscreen_settings_screen_list_preview() {
        snapshot {
            FullscreenSettingsScreenListPreview()
        }
    }

    @Test
    fun fullscreen_settings_screen_algorithm_preview() {
        snapshot {
            FullscreenSettingsScreenAlgorithmPreview()
        }
    }

    @Test
    fun fullscreen_settings_screen_visual_preview() {
        snapshot {
            FullscreenSettingsScreenVisualPreview()
        }
    }

    @Test
    fun fullscreen_settings_screen_feature_flags_preview() {
        snapshot {
            FullscreenSettingsScreenFeatureFlagsPreview()
        }
    }
}

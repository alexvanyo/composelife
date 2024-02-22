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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.foundation.layout.padding
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.util.BaseRoborazziTest
import com.alexvanyo.composelife.ui.app.util.RoborazziParameterization
import kotlin.test.Test

class ClipboardWatchingSectionSnapshotTests(
    roborazziParameterization: RoborazziParameterization,
) : BaseRoborazziTest(roborazziParameterization) {

    @Test
    fun clipboard_watching_section_onboarding_preview() {
        snapshot {
            ClipboardWatchingSectionOnboardingPreview()
        }
    }

    @Test
    fun clipboard_watching_section_disabled_preview() {
        snapshot {
            ClipboardWatchingSectionDisabledPreview(
                modifier = Modifier.padding(1.dp),
            )
        }
    }

    @Test
    fun clipboard_watching_section_enabled_loading_preview() {
        snapshot {
            ClipboardWatchingSectionEnabledLoadingPreview()
        }
    }

    @Test
    fun clipboard_watching_section_enabled_failure_preview() {
        snapshot {
            ClipboardWatchingSectionEnabledFailurePreview()
        }
    }

    @Test
    fun clipboard_watching_section_enabled_success_successful_preview() {
        snapshot {
            ClipboardWatchingSectionEnabledSuccessSuccessfulPreview()
        }
    }
}

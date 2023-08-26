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

package com.alexvanyo.composelife.ui.app.action

import com.alexvanyo.composelife.ui.app.util.BaseRoborazziTest
import kotlin.test.Test

class InlineEditScreenSnapshotTests(
    deviceName: String,
    deviceQualifiers: String,
    darkTheme: Boolean,
    fontScale: Float,
) : BaseRoborazziTest(deviceName, deviceQualifiers, darkTheme, fontScale) {

    @Test
    fun inline_edit_screen_preview() {
        snapshot {
            InlineEditScreenPreview()
        }
    }
}

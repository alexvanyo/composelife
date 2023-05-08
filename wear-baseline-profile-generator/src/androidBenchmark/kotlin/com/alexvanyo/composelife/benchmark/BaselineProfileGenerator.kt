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

package com.alexvanyo.composelife.benchmark

import android.content.ComponentName
import androidx.benchmark.macro.ExperimentalStableBaselineProfilesApi
import androidx.benchmark.macro.junit4.BaselineProfileRule
import androidx.test.platform.app.InstrumentationRegistry
import androidx.wear.watchface.editor.EditorRequest
import androidx.wear.watchface.editor.WatchFaceEditorContract
import org.junit.Rule
import kotlin.test.Test

class BaselineProfileGenerator {

    @get:Rule
    val baselineProfileRule = BaselineProfileRule()

    @OptIn(ExperimentalStableBaselineProfilesApi::class)
    @Test
    fun startup() {
        baselineProfileRule.collectStableBaselineProfile(
            packageName = "com.alexvanyo.composelife.wear",
            maxIterations = 10,
        ) {
            InstrumentationRegistry.getInstrumentation().uiAutomation.executeShellCommand(
                "am broadcast -a com.google.android.wearable.app.DEBUG_SURFACE " +
                    "--es operation set-watchface " +
                    "--ecn component com.alexvanyo.composelife.wear/" +
                    "com.alexvanyo.composelife.wear.watchface.GameOfLifeWatchFaceService",
            )
            startActivityAndWait(
                WatchFaceEditorContract().createIntent(
                    InstrumentationRegistry.getInstrumentation().context,
                    EditorRequest(
                        watchFaceComponentName = ComponentName(
                            "com.alexvanyo.composelife.wear",
                            "com.alexvanyo.composelife.wear.watchface.GameOfLifeWatchFaceService",
                        ),
                        editorPackageName = "com.alexvanyo.composelife.wear",
                        initialUserStyle = null,
                    ),
                ),
            )
        }
    }
}

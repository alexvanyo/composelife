/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.navigation

import androidx.compose.foundation.clickable
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.retain.RetainedContentHost
import androidx.compose.runtime.retain.retain
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import kotlin.test.Ignore
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
class RetainTests : BaseKmpTest() {

    @Ignore
    @Test
    fun simple_retained_content_host() = runComposeUiTest {
        var isActive by mutableStateOf(false)
        setContent {
            RetainedContentHost(isActive) {
                var count by retain { mutableStateOf(0) }
                BasicText(
                    "count: $count",
                    modifier = Modifier.clickable {
                        count++
                    },
                )
            }
        }

        onNodeWithText("count: 0").assertDoesNotExist()

        isActive = true

        onNodeWithText("count: 0").assertExists()
        onNodeWithText("count: 0").performClick()
        onNodeWithText("count: 1").assertExists()

        isActive = false

        onNodeWithText("count: 1").assertDoesNotExist()

        isActive = true

        onNodeWithText("count: 1").assertExists()
    }
}

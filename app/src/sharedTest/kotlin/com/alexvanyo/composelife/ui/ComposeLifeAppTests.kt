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

package com.alexvanyo.composelife.ui

import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import com.alexvanyo.composelife.MainActivity
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.test.BaseHiltTest
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import org.junit.Test

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class ComposeLifeAppTests : BaseHiltTest<MainActivity>(MainActivity::class.java) {

    @Test
    fun app_does_not_crash() = runAppTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.waitForIdle()
    }

    @Test
    fun app_does_not_crash_when_recreating() = runAppTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.activityRule.scenario.recreate()

        composeTestRule.waitForIdle()
    }
}

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

package com.alexvanyo.composelife.ui.util

import android.app.Application
import android.content.Intent
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import kotlinx.datetime.TimeZone
import kotlinx.datetime.toJavaZoneId
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(AndroidJUnit4::class)
class TimeZoneTests {

    @Test
    fun time_zone_updates_correctly() = runComposeUiTest {
        val systemDefaultTimeZone = TimeZone.currentSystemDefault()
        var timeZone: TimeZone by mutableStateOf(TimeZone.UTC)

        setContent {
            timeZone = currentTimeZone()
        }

        assertEquals(systemDefaultTimeZone, timeZone)

        val newTimeZone = TimeZone.of("GMT+1")
        try {
            java.util.TimeZone.setDefault(java.util.TimeZone.getTimeZone(newTimeZone.toJavaZoneId()))

            ApplicationProvider.getApplicationContext<Application>()
                .sendBroadcast(Intent(Intent.ACTION_TIMEZONE_CHANGED))

            waitForIdle()

            assertEquals(newTimeZone, timeZone)
        } finally {
            java.util.TimeZone.setDefault(java.util.TimeZone.getTimeZone(systemDefaultTimeZone.toJavaZoneId()))
        }
    }
}

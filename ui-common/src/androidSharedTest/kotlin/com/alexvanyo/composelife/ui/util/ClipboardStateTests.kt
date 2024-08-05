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

package com.alexvanyo.composelife.ui.util

import android.content.ClipData
import android.content.ClipboardManager
import androidx.activity.ComponentActivity
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runAndroidComposeUiTest
import androidx.core.content.getSystemService
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ClipboardStateTests {

    @Test
    fun reading_from_clipboard_state_is_correct() = runAndroidComposeUiTest<ComponentActivity> {
        var clipData: ClipData? = null

        setContent {
            clipData = rememberClipboardReader().getClipData()
        }

        val clipboardManager = requireNotNull(activity!!.getSystemService<ClipboardManager>())
        val testClipData = ClipData.newPlainText("test clip data", "test value 1")
        clipboardManager.setPrimaryClip(testClipData)

        waitForIdle()

        val actualClipData = clipData
        assertNotNull(actualClipData)
        assertEquals(testClipData.itemCount, actualClipData.itemCount)
        repeat(actualClipData.itemCount) {
            assertEquals(testClipData.getItemAt(it).text, actualClipData.getItemAt(it).text)
        }
    }

    @Test
    fun writing_to_clipboard_state_is_correct() = runAndroidComposeUiTest<ComponentActivity> {
        lateinit var clipboardWriter: ClipboardWriter

        val testClipData = ClipData.newPlainText("test clip data", "test value 2")

        setContent {
            clipboardWriter = rememberClipboardWriter()
            LaunchedEffect(Unit) {
                clipboardWriter.setClipData(testClipData)
            }
        }

        val clipboardManager = requireNotNull(activity!!.getSystemService<ClipboardManager>())

        val actualClipData = clipboardManager.primaryClip
        assertNotNull(actualClipData)
        assertEquals(testClipData.itemCount, actualClipData.itemCount)
        repeat(actualClipData.itemCount) {
            assertEquals(testClipData.getItemAt(it).text, actualClipData.getItemAt(it).text)
        }
    }
}

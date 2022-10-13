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

package com.alexvanyo.composelife.snapshotstateset

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import kotlin.test.Test
import kotlin.test.assertEquals

@Suppress("UnnecessaryAbstractClass")
@OptIn(ExperimentalTestApi::class)
abstract class BaseSnapshotStateSetTests {

    @Test
    fun collect_as_state_is_correct() {
        runComposeUiTest {
            val set = mutableStateSetOf<Int>()
            var values: List<Int>? = null

            setContent {
                values = set.toList()
            }

            waitForIdle()
            assertEquals(emptyList(), values)

            set.add(1)

            waitForIdle()
            assertEquals(listOf(1), values)
        }
    }
}

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

import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.ui.unit.dp
import kotlin.test.Test
import kotlin.test.assertEquals

class WindowInsetsExtensionsTests {

    @Test
    fun zero_is_correct() {
        assertEquals(
            WindowInsets(0, 0, 0, 0),
            WindowInsets.Zero,
        )
    }

    @Test
    fun all_dp_is_correct() {
        assertEquals(
            WindowInsets(5.dp, 5.dp, 5.dp, 5.dp),
            WindowInsets(all = 5.dp),
        )
    }
}

/*
 * Copyright 2026 The Android Open Source Project
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
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.v2.runComposeUiTest
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

@OptIn(ExperimentalTestApi::class)
class LocalWindowInsetsTests {

    @Test
    fun parse_px_handles_valid_pixels() {
        assertEquals(47f, parsePx("47px"))
        assertEquals(0f, parsePx("0px"))
        assertEquals(34.5f, parsePx("34.5px"))
        assertEquals(12f, parsePx("  12px  "))
    }

    @Test
    fun parse_px_handles_invalid_or_empty() {
        assertEquals(0f, parsePx(""))
        assertEquals(0f, parsePx("none"))
        assertEquals(0f, parsePx("auto"))
    }

    @Test
    fun provide_local_window_insets_holder_provides_insets() = runComposeUiTest {
        setContent {
            ProvideLocalWindowInsetsHolder {
                val holder = LocalWindowInsetsHolder.current
                assertNotNull(holder)
                val safeDrawing = WindowInsets.safeDrawing
                assertNotNull(safeDrawing)
                // In headless browser test, default insets evaluate to a valid integer
                val top = safeDrawing.getTop(Density(1f))
                val bottom = safeDrawing.getBottom(Density(1f))
                val left = safeDrawing.getLeft(Density(1f), LayoutDirection.Ltr)
                val right = safeDrawing.getRight(Density(1f), LayoutDirection.Ltr)
                assertEquals(0, top)
                assertEquals(0, bottom)
                assertEquals(0, left)
                assertEquals(0, right)
            }
        }
    }
}

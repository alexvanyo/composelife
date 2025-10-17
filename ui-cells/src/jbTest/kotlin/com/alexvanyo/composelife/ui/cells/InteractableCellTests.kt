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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.preferences.CurrentShape
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
class InteractableCellTests : BaseKmpTest() {

    @Test
    fun alive_cell_calls_correct_function() = runComposeUiTest {
        var onValueChangeResult: Boolean? = null

        setContent {
            InteractableCell(
                modifier = Modifier
                    .size(32.dp),
                drawState = DrawState.Alive,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it },
            )
        }

        onNodeWithContentDescription("test cell")
            .assertIsOn()
            .performClick()

        assertEquals(false, onValueChangeResult)
    }

    @Test
    fun dead_cell_calls_correct_function() = runComposeUiTest {
        var onValueChangeResult: Boolean? = null

        setContent {
            InteractableCell(
                modifier = Modifier
                    .size(32.dp),
                drawState = DrawState.Dead,
                shape = CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
                contentDescription = "test cell",
                onValueChange = { onValueChangeResult = it },
            )
        }

        onNodeWithContentDescription("test cell")
            .assertIsOff()
            .performClick()

        assertEquals(true, onValueChangeResult)
    }
}

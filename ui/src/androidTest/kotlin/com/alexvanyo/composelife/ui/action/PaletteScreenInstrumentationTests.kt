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

package com.alexvanyo.composelife.ui.action

import android.app.Application
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class PaletteScreenInstrumentationTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val applicationContext = ApplicationProvider.getApplicationContext<Application>()

    @Test
    fun round_rectangle_popup_displays_options() {
        var setCurrentShapeType: CurrentShapeType? = null

        composeTestRule.setContent {
            InlinePaletteScreen(
                currentShapeState = ResourceState.Success(
                    CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.4f,
                    ),
                ),
                setCurrentShapeType = {
                    setCurrentShapeType = it
                },
                setRoundRectangleConfig = {},
            )
        }

        composeTestRule
            .onNodeWithText(applicationContext.getString(R.string.round_rectangle))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(applicationContext.getString(R.string.round_rectangle)))
            .assertHasClickAction()
            .performClick()

        assertEquals(CurrentShapeType.RoundRectangle, setCurrentShapeType)

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()
    }
}

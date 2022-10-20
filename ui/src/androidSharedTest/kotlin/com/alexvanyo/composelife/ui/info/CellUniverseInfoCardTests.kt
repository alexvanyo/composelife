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

package com.alexvanyo.composelife.ui.info

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsEnabled
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.assertIsToggleable
import androidx.compose.ui.test.isToggleable
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test

@RunWith(AndroidJUnit4::class)
class CellUniverseInfoCardTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun card_is_collapsed_by_default() {
        composeTestRule.setContent {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.expand))
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsEnabled()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.collapse))
            .assertDoesNotExist()
    }

    @Test
    fun card_becomes_expanded_when_expand_button_is_clicked() {
        composeTestRule.setContent {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.expand))
            .performClick()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.collapse))
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsEnabled()

        composeTestRule.onNodeWithContentDescription(context.getString(R.string.expand))
            .assertDoesNotExist()
    }

    @Test
    fun card_hides_checkboxes_when_collapsed() {
        composeTestRule.setContent {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = false),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }

        composeTestRule.onNodeWithText("First")
            .assert(isToggleable().not())

        composeTestRule.onNodeWithText("Second")
            .assert(isToggleable().not())

        composeTestRule.onNodeWithText("Third")
            .assert(isToggleable().not())
    }

    @Test
    fun card_show_checkboxes_when_expanded() {
        composeTestRule.setContent {
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    rememberCellUniverseInfoCardState(initialIsExpanded = true),
                    cellUniverseInfoItemContents = listOf(
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "First" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Second" },
                        CellUniverseInfoItemContent(
                            rememberCellUniverseInfoItemState(),
                        ) { "Third" },
                    ),
                ),
            )
        }

        composeTestRule.onNodeWithText("First")
            .assertIsToggleable()
            .assertIsOn()

        composeTestRule.onNodeWithText("Second")
            .assertIsToggleable()
            .assertIsOn()

        composeTestRule.onNodeWithText("Third")
            .assertIsToggleable()
            .assertIsOn()
    }
}

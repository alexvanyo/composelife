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

package com.alexvanyo.composelife.ui.app.info

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsEnabled
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.assertIsToggleable
import androidx.compose.ui.test.isToggleable
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.resources.Collapse
import com.alexvanyo.composelife.ui.app.resources.Expand
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.util.TargetState
import org.junit.runner.RunWith
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class CellUniverseInfoCardTests {

    @Test
    fun card_is_collapsed_by_default() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()

            var isExpanded by rememberSaveable { mutableStateOf(false) }
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = { isExpanded = it },
                        expandedTargetState = TargetState.Single(isExpanded),
                    ),
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

        onNodeWithContentDescription(resolver(Strings.Expand))
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsEnabled()

        onNodeWithContentDescription(resolver(Strings.Collapse))
            .assertDoesNotExist()
    }

    @Test
    fun card_becomes_expanded_when_expand_button_is_clicked() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()

            var isExpanded by rememberSaveable { mutableStateOf(false) }
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = { isExpanded = it },
                        expandedTargetState = TargetState.Single(isExpanded),
                    ),
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

        onNodeWithContentDescription(resolver(Strings.Expand))
            .performClick()

        onNodeWithContentDescription(resolver(Strings.Collapse))
            .assertIsDisplayed()
            .assertHasClickAction()
            .assertIsEnabled()

        onNodeWithContentDescription(resolver(Strings.Expand))
            .assertDoesNotExist()
    }

    @Test
    fun card_hides_checkboxes_when_collapsed() = runComposeUiTest {
        setContent {
            var isExpanded by rememberSaveable { mutableStateOf(false) }
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = { isExpanded = it },
                        expandedTargetState = TargetState.Single(isExpanded),
                    ),
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

        onNodeWithText("First")
            .assert(isToggleable().not())

        onNodeWithText("Second")
            .assert(isToggleable().not())

        onNodeWithText("Third")
            .assert(isToggleable().not())
    }

    @Test
    fun card_show_checkboxes_when_expanded() = runComposeUiTest {
        setContent {
            var isExpanded by rememberSaveable { mutableStateOf(true) }
            CellUniverseInfoCard(
                cellUniverseInfoCardContent = CellUniverseInfoCardContent(
                    cellUniverseInfoCardState = rememberCellUniverseInfoCardState(
                        setIsExpanded = { isExpanded = it },
                        expandedTargetState = TargetState.Single(isExpanded),
                    ),
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

        onNodeWithText("First")
            .assertIsToggleable()
            .assertIsOn()

        onNodeWithText("Second")
            .assertIsToggleable()
            .assertIsOn()

        onNodeWithText("Third")
            .assertIsToggleable()
            .assertIsOn()
    }
}

/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.ForcedSize
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.resources.Back
import com.alexvanyo.composelife.ui.app.resources.Close
import com.alexvanyo.composelife.ui.app.resources.DeserializationFailed
import com.alexvanyo.composelife.ui.app.resources.DeserializationSucceeded
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class DeserializationInfoPaneTests {

    @Test
    fun successful_is_displayed_correctly_in_dialog() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(1200.dp, 800.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = emptyCellState(),
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {},
                    )
                }
            }
        }

        onNodeWithText(resolver(Strings.DeserializationSucceeded))
            .assertIsDisplayed()

        onNodeWithContentDescription(resolver(Strings.Close))
            .assertHasClickAction()

        onNodeWithText("Warning 1")
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    fun successful_is_displayed_correctly_not_in_dialog() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(400.dp, 400.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = emptyCellState(),
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {},
                    )
                }
            }
        }

        onNodeWithText(resolver(Strings.DeserializationSucceeded))
            .assertIsDisplayed()

        onNodeWithContentDescription(resolver(Strings.Back))
            .assertHasClickAction()

        onNodeWithText("Warning 1")
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    fun unsuccessful_is_displayed_correctly_in_dialog() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(1200.dp, 800.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Unsuccessful(
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                                errors = listOf(
                                    ParameterizedString("Error 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {},
                    )
                }
            }
        }

        onNodeWithText(resolver(Strings.DeserializationFailed))
            .assertIsDisplayed()

        onNodeWithContentDescription(resolver(Strings.Close))
            .assertHasClickAction()

        onNodeWithText("Warning 1")
            .performScrollTo()
            .assertIsDisplayed()

        onNodeWithText("Error 1")
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    fun unsuccessful_is_displayed_correctly_not_in_dialog() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(400.dp, 400.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Unsuccessful(
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                                errors = listOf(
                                    ParameterizedString("Error 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {},
                    )
                }
            }
        }

        onNodeWithText(resolver(Strings.DeserializationFailed))
            .assertIsDisplayed()

        onNodeWithContentDescription(resolver(Strings.Back))
            .assertHasClickAction()

        onNodeWithText("Warning 1")
            .performScrollTo()
            .assertIsDisplayed()

        onNodeWithText("Error 1")
            .performScrollTo()
            .assertIsDisplayed()
    }

    @Test
    fun close_button_clicked_in_dialog() = runComposeUiTest {
        var closeButtonWasClicked = false

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(1200.dp, 800.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = emptyCellState(),
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {
                            closeButtonWasClicked = true
                        },
                    )
                }
            }
        }

        onNodeWithContentDescription(resolver(Strings.Close))
            .performClick()

        assertTrue(closeButtonWasClicked)
    }

    @Test
    fun back_button_clicked_not_in_dialog() = runComposeUiTest {
        var backButtonWasClicked = false

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            DeviceConfigurationOverride(
                DeviceConfigurationOverride.ForcedSize(DpSize(400.dp, 400.dp)),
            ) {
                BoxWithConstraints {
                    val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                        maxWidth.value,
                        maxHeight.value,
                    )
                    val navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = emptyCellState(),
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                ),
                            ),
                        ),
                        windowSizeClass = windowSizeClass,
                    )
                    DeserializationInfoPane(
                        navEntryValue = navEntryValue,
                        onBackButtonPressed = {
                            backButtonWasClicked = true
                        },
                    )
                }
            }
        }

        onNodeWithContentDescription(resolver(Strings.Back))
            .performClick()

        assertTrue(backButtonWasClicked)
    }
}

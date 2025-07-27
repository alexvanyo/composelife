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

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews

@ShowkaseComposable
@MobileDevicePreviews
@Composable
internal fun SuccessfulDeserializationInfoPanePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier = modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                DeserializationInfoPane(
                    navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = emptyCellState(),
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                    ParameterizedString("Warning 2"),
                                ),
                            ),
                        ),
                        windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                            widthDp = size.width,
                            heightDp = size.height,
                        ),
                    ),
                    onBackButtonPressed = {},
                )
            }
        }
    }
}

@ShowkaseComposable
@MobileDevicePreviews
@Composable
internal fun UnsuccessfulDeserializationInfoPanePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier = modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                DeserializationInfoPane(
                    navEntryValue = ComposeLifeUiNavigation.DeserializationInfo(
                        nav = ComposeLifeNavigation.DeserializationInfo(
                            deserializationResult = DeserializationResult.Unsuccessful(
                                warnings = listOf(
                                    ParameterizedString("Warning 1"),
                                    ParameterizedString("Warning 2"),
                                ),
                                errors = listOf(
                                    ParameterizedString("Error 1"),
                                    ParameterizedString("Error 2"),
                                ),
                            ),
                        ),
                        windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                            widthDp = size.width,
                            heightDp = size.height,
                        ),
                    ),
                    onBackButtonPressed = {},
                )
            }
        }
    }
}

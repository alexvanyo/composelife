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
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.scopes.implicit
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews

@ShowkaseComposable
@MobileDevicePreviews
@Composable
internal fun LoadingCellStateCellUniversePanePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        implicit().testRandom.setSeed(1) // Fix to Beacon loading pattern
        ComposeLifeTheme {
            with(implicit().cellUniversePaneEntryPoint) {
                BoxWithConstraints(modifier = modifier) {
                    val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                    CellUniversePane(
                        windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                            widthDp = size.width,
                            heightDp = size.height,
                        ),
                        onSeeMoreSettingsClicked = {},
                        onOpenInSettingsClicked = {},
                        onViewDeserializationInfo = {},
                        cellUniversePaneState = CellUniversePaneState.LoadingCellState,
                    )
                }
            }
        }
    }
}

@ShowkaseComposable
@MobileDevicePreviews
@Composable
internal fun LoadedCellUniversePanePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            with(implicit().cellUniversePaneEntryPoint) {
                BoxWithConstraints(modifier = modifier) {
                    val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                    val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                        seedCellState = gosperGliderGun,
                        isRunning = false,
                    )
                    CellUniversePane(
                        windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                            widthDp = size.width,
                            heightDp = size.height,
                        ),
                        onSeeMoreSettingsClicked = {},
                        onOpenInSettingsClicked = {},
                        onViewDeserializationInfo = {},
                        cellUniversePaneState = object : CellUniversePaneState.LoadedCellState {
                            override val temporalGameOfLifeState = temporalGameOfLifeState
                        },
                    )
                }
            }
        }
    }
}

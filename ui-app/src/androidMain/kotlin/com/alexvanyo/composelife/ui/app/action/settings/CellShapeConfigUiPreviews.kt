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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.benasher44.uuid.uuid4

@ThemePreviews
@Composable
fun CellShapeConfigUiRoundRectanglePreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface(modifier) {
                CellShapeConfigUi(
                    cellShapeConfigUiState = object : CellShapeConfigUiState {
                        override val currentShapeDropdownOption = ShapeDropdownOption.RoundRectangle
                        override val currentShapeConfigUiState =
                            object : CurrentShapeConfigUiState.RoundRectangleConfigUi {
                                override val sizeFractionSessionValue =
                                    SessionValue(uuid4(), uuid4(), 0.8f)
                                override val cornerFractionSessionValue =
                                    SessionValue(uuid4(), uuid4(), 0.4f)

                                override fun onSizeFractionSessionValueChange(value: SessionValue<Float>) = Unit
                                override fun onCornerFractionSessionValueChange(value: SessionValue<Float>) = Unit
                            }
                        override fun setCurrentShapeType(option: ShapeDropdownOption) = Unit
                    },
                )
            }
        }
    }
}

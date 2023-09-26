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
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ThemePreviews
@Composable
fun CellShapeConfigUiRoundRectanglePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                CellShapeConfigUi(
                    currentShape = CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.4f,
                    ),
                    setCurrentShapeType = {},
                    setRoundRectangleConfig = {},
                )
            }
        }
    }
}

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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Analytics
import androidx.compose.material.icons.filled.Flag
import androidx.compose.material.icons.filled.Palette
import androidx.compose.material.icons.outlined.Analytics
import androidx.compose.material.icons.outlined.Flag
import androidx.compose.material.icons.outlined.Palette
import androidx.compose.runtime.Composable
import androidx.compose.ui.graphics.vector.ImageVector
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.resources.Algorithm
import com.alexvanyo.composelife.ui.app.resources.FeatureFlags
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Visual

val SettingsCategory.title: String
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> parameterizedStringResource(Strings.Algorithm)
        SettingsCategory.FeatureFlags -> parameterizedStringResource(Strings.FeatureFlags)
        SettingsCategory.Visual -> parameterizedStringResource(Strings.Visual)
    }

val SettingsCategory.filledIcon: ImageVector
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> Icons.Filled.Analytics
        SettingsCategory.FeatureFlags -> Icons.Filled.Flag
        SettingsCategory.Visual -> Icons.Filled.Palette
    }

val SettingsCategory.outlinedIcon: ImageVector
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> Icons.Outlined.Analytics
        SettingsCategory.FeatureFlags -> Icons.Outlined.Flag
        SettingsCategory.Visual -> Icons.Outlined.Palette
    }

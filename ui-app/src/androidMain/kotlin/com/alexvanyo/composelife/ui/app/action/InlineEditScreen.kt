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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Backspace
import androidx.compose.material.icons.filled.Brush
import androidx.compose.material.icons.filled.Cancel
import androidx.compose.material.icons.filled.Draw
import androidx.compose.material.icons.filled.Mouse
import androidx.compose.material.icons.filled.PanTool
import androidx.compose.material.icons.filled.SelectAll
import androidx.compose.material.icons.filled.TouchApp
import androidx.compose.material3.Icon
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.livefront.sealedenum.GenSealedEnum

@Composable
fun InlineEditScreen(
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier
            .verticalScroll(scrollState)
            .padding(vertical = 8.dp),
    ) {
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.TouchApp,
                contentDescription = stringResource(R.string.touch),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = stringResource(R.string.touch_tool),
                currentValue = ToolDropdownOption.Pan,
                allValues = ToolDropdownOption.values,
                setValue = {},
            )
        }
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.Brush,
                contentDescription = stringResource(R.string.stylus),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = stringResource(R.string.stylus_tool),
                currentValue = ToolDropdownOption.Draw,
                allValues = ToolDropdownOption.values,
                setValue = {},
            )
        }
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.Mouse,
                contentDescription = stringResource(R.string.mouse),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = stringResource(R.string.mouse_tool),
                currentValue = ToolDropdownOption.Draw,
                allValues = ToolDropdownOption.values,
                setValue = {},
            )
        }
    }
}

sealed interface ToolDropdownOption : DropdownOption {
    object Pan : ToolDropdownOption {
        override val displayText = ParameterizedString(R.string.pan)
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.PanTool,
                contentDescription = null,
            )
        }
    }
    object Draw : ToolDropdownOption {
        override val displayText = ParameterizedString(R.string.draw)
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Draw,
                contentDescription = null,
            )
        }
    }
    object Erase : ToolDropdownOption {
        override val displayText = ParameterizedString(R.string.erase)
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Backspace,
                contentDescription = null,
            )
        }
    }
    object Select : ToolDropdownOption {
        override val displayText = ParameterizedString(R.string.select)
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.SelectAll,
                contentDescription = null,
            )
        }
    }
    object None : ToolDropdownOption {
        override val displayText = ParameterizedString(R.string.none)
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Cancel,
                contentDescription = null,
            )
        }
    }

    @GenSealedEnum
    companion object
}

@ThemePreviews
@Composable
fun InlineEditScreenPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                InlineEditScreen()
            }
        }
    }
}

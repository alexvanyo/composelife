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
import androidx.compose.material.icons.filled.Brush
import androidx.compose.material.icons.filled.Cancel
import androidx.compose.material.icons.filled.Draw
import androidx.compose.material.icons.filled.Mouse
import androidx.compose.material.icons.filled.PanTool
import androidx.compose.material.icons.filled.SelectAll
import androidx.compose.material.icons.filled.TouchApp
import androidx.compose.material3.Icon
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.resources.Draw
import com.alexvanyo.composelife.ui.app.resources.Erase
import com.alexvanyo.composelife.ui.app.resources.Mouse
import com.alexvanyo.composelife.ui.app.resources.MouseTool
import com.alexvanyo.composelife.ui.app.resources.None
import com.alexvanyo.composelife.ui.app.resources.Pan
import com.alexvanyo.composelife.ui.app.resources.Select
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Stylus
import com.alexvanyo.composelife.ui.app.resources.StylusTool
import com.alexvanyo.composelife.ui.app.resources.Touch
import com.alexvanyo.composelife.ui.app.resources.TouchTool
import com.alexvanyo.composelife.ui.util.autoMirrored
import com.alexvanyo.composelife.ui.util.filled
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.collections.immutable.toImmutableList

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
                contentDescription = parameterizedStringResource(Strings.Touch),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.TouchTool),
                currentValue = ToolDropdownOption.Pan,
                allValues = ToolDropdownOption.values.toImmutableList(),
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
                contentDescription = parameterizedStringResource(Strings.Stylus),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.StylusTool),
                currentValue = ToolDropdownOption.Draw,
                allValues = ToolDropdownOption.values.toImmutableList(),
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
                contentDescription = parameterizedStringResource(Strings.Mouse),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.MouseTool),
                currentValue = ToolDropdownOption.Draw,
                allValues = ToolDropdownOption.values.toImmutableList(),
                setValue = {},
            )
        }
    }
}

sealed interface ToolDropdownOption : DropdownOption {
    data object Pan : ToolDropdownOption {
        override val displayText = Strings.Pan
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.PanTool,
                contentDescription = null,
            )
        }
    }
    data object Draw : ToolDropdownOption {
        override val displayText = Strings.Draw
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Draw,
                contentDescription = null,
            )
        }
    }
    data object Erase : ToolDropdownOption {
        override val displayText = Strings.Erase
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.autoMirrored.filled.Backspace,
                contentDescription = null,
            )
        }
    }
    data object Select : ToolDropdownOption {
        override val displayText = Strings.Select
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.SelectAll,
                contentDescription = null,
            )
        }
    }
    data object None : ToolDropdownOption {
        override val displayText = Strings.None
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

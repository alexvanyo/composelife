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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Text
import androidx.compose.material3.TextFieldDefaults
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import kotlinx.collections.immutable.ImmutableList

/**
 * An option in a [TextFieldDropdown].
 */
interface DropdownOption {
    /**
     * The text to display for the [DropdownOption].
     */
    val displayText: ParameterizedString

    /**
     * The leading icon (if any) to display for the [DropdownOption].
     */
    val leadingIcon: (@Composable () -> Unit)? get() = null
}

/**
 * A styled drop-down menu to select between [allValues], with the given [currentValue].
 */
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun <T : DropdownOption> TextFieldDropdown(
    label: String,
    currentValue: T,
    allValues: ImmutableList<T>,
    setValue: (T) -> Unit,
    modifier: Modifier = Modifier,
) {
    var isShowingDropdownMenu by remember { mutableStateOf(false) }

    Box(modifier = modifier) {
        OutlinedTextField(
            value = parameterizedStringResource(currentValue.displayText),
            onValueChange = {},
            enabled = false,
            readOnly = true,
            label = {
                Text(text = label)
            },
            leadingIcon = currentValue.leadingIcon,
            trailingIcon = {
                Icon(
                    if (isShowingDropdownMenu) {
                        Icons.Default.ArrowDropUp
                    } else {
                        Icons.Default.ArrowDropDown
                    },
                    contentDescription = null,
                )
            },
            colors = TextFieldDefaults.outlinedTextFieldColors(
                containerColor = MaterialTheme.colorScheme.surfaceVariant,
                disabledBorderColor = MaterialTheme.colorScheme.outline,
                disabledTextColor = MaterialTheme.colorScheme.onSurfaceVariant,
                disabledTrailingIconColor = MaterialTheme.colorScheme.onSurfaceVariant,
                disabledLabelColor = MaterialTheme.colorScheme.onSurfaceVariant,
            ),
            singleLine = true,
            modifier = Modifier
                .fillMaxWidth()
                .clickable {
                    isShowingDropdownMenu = true
                },
        )

        DropdownMenu(
            expanded = isShowingDropdownMenu,
            onDismissRequest = { isShowingDropdownMenu = false },
        ) {
            allValues.forEach { value ->
                DropdownMenuItem(
                    text = { Text(parameterizedStringResource(value.displayText)) },
                    leadingIcon = value.leadingIcon,
                    onClick = {
                        setValue(value)
                        isShowingDropdownMenu = false
                    },
                )
            }
        }
    }
}

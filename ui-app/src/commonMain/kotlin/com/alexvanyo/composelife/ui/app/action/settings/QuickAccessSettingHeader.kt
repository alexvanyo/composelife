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

import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.width
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Bookmark
import androidx.compose.material.icons.filled.OpenInFull
import androidx.compose.material.icons.outlined.BookmarkBorder
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.component.HorizontalDivider
import com.alexvanyo.composelife.ui.app.component.PlainTooltipBox
import com.alexvanyo.composelife.ui.app.resources.AddSettingToQuickAccess
import com.alexvanyo.composelife.ui.app.resources.OpenInSettings
import com.alexvanyo.composelife.ui.app.resources.RemoveSettingFromQuickAccess
import com.alexvanyo.composelife.ui.app.resources.Strings

@OptIn(ExperimentalMaterial3Api::class)
@Suppress("LongMethod")
@Composable
fun QuickAccessSettingHeader(
    isFavorite: Boolean,
    setIsFavorite: (Boolean) -> Unit,
    modifier: Modifier = Modifier,
    onOpenInSettingsClicked: (() -> Unit)? = null,
) {
    Row(
        modifier = modifier.fillMaxWidth(),
        verticalAlignment = Alignment.CenterVertically,
    ) {
        HorizontalDivider(
            modifier = Modifier.weight(1f),
            color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
        )

        if (onOpenInSettingsClicked != null) {
            PlainTooltipBox(
                tooltip = {
                    Text(parameterizedStringResource(Strings.OpenInSettings))
                },
            ) {
                IconButton(
                    onClick = onOpenInSettingsClicked,
                    modifier = Modifier.tooltipAnchor(),
                ) {
                    Icon(
                        imageVector = Icons.Default.OpenInFull,
                        contentDescription = parameterizedStringResource(Strings.OpenInSettings),
                    )
                }
            }
            HorizontalDivider(
                color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
                modifier = Modifier.width(16.dp),
            )
        }

        PlainTooltipBox(
            tooltip = {
                Text(
                    parameterizedStringResource(
                        if (isFavorite) {
                            Strings.RemoveSettingFromQuickAccess
                        } else {
                            Strings.AddSettingToQuickAccess
                        },
                    ),
                )
            },
        ) {
            IconToggleButton(
                checked = isFavorite,
                onCheckedChange = setIsFavorite,
                modifier = Modifier.tooltipAnchor(),
            ) {
                Icon(
                    imageVector = if (isFavorite) {
                        Icons.Filled.Bookmark
                    } else {
                        Icons.Outlined.BookmarkBorder
                    },
                    contentDescription = parameterizedStringResource(
                        if (isFavorite) {
                            Strings.RemoveSettingFromQuickAccess
                        } else {
                            Strings.AddSettingToQuickAccess
                        },
                    ),
                )
            }
        }

        HorizontalDivider(
            color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
            modifier = Modifier.width(16.dp),
        )
    }
}

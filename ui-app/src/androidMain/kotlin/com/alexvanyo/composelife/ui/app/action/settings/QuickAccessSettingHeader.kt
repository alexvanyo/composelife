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
import androidx.compose.material3.Divider
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

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
        Divider(
            modifier = Modifier.weight(1f),
            color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
        )

        if (onOpenInSettingsClicked != null) {
            IconButton(onClick = onOpenInSettingsClicked) {
                Icon(
                    imageVector = Icons.Default.OpenInFull,
                    contentDescription = stringResource(id = R.string.open_in_settings),
                )
            }
            Divider(
                color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
                modifier = Modifier.width(16.dp),
            )
        }

        IconToggleButton(
            checked = isFavorite,
            onCheckedChange = setIsFavorite,
        ) {
            Icon(
                imageVector = if (isFavorite) {
                    Icons.Filled.Bookmark
                } else {
                    Icons.Outlined.BookmarkBorder
                },
                contentDescription = if (isFavorite) {
                    stringResource(id = R.string.remove_setting_from_quick_access)
                } else {
                    stringResource(id = R.string.add_setting_to_quick_access)
                },
            )
        }

        Divider(
            color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
            modifier = Modifier.width(16.dp),
        )
    }
}

@ThemePreviews
@Composable
fun QuickAccessSettingHeaderIsFavoritePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                QuickAccessSettingHeader(
                    isFavorite = true,
                    setIsFavorite = {},
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun QuickAccessSettingHeaderWithOpenInSettingsPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                QuickAccessSettingHeader(
                    isFavorite = true,
                    setIsFavorite = {},
                    onOpenInSettingsClicked = {},
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun QuickAccessSettingHeaderIsNotFavoritePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                QuickAccessSettingHeader(
                    isFavorite = false,
                    setIsFavorite = {},
                )
            }
        }
    }
}

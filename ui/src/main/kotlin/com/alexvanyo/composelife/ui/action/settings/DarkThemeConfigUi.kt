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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
import androidx.compose.material3.Icon
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.OutlinedTextField
import androidx.compose.material3.Text
import androidx.compose.material3.TextFieldDefaults
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.entrypoints.preferences.inject
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import kotlinx.coroutines.launch

@Composable
fun DarkThemeConfigUi(
    modifier: Modifier = Modifier,
    composeLifePreferences: ComposeLifePreferences = inject(),
) {
    DarkThemeConfigUi(
        darkThemeConfigState = composeLifePreferences.darkThemeConfigState,
        setDarkThemeConfig = composeLifePreferences::setDarkThemeConfig,
        modifier = modifier,
    )
}

@Suppress("LongMethod")
@Composable
fun DarkThemeConfigUi(
    darkThemeConfigState: ResourceState<DarkThemeConfig>,
    setDarkThemeConfig: suspend (DarkThemeConfig) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        when (darkThemeConfigState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                CircularProgressIndicator()
            }

            is ResourceState.Success -> {
                val currentDarkThemeConfig = darkThemeConfigState.value
                val coroutineScope = rememberCoroutineScope()

                var isShowingDropdownMenu by remember { mutableStateOf(false) }

                Box {
                    OutlinedTextField(
                        value = stringResource(
                            id = when (currentDarkThemeConfig) {
                                DarkThemeConfig.FollowSystem -> R.string.follow_system
                                DarkThemeConfig.Dark -> R.string.dark_theme
                                DarkThemeConfig.Light -> R.string.light_theme
                            },
                        ),
                        onValueChange = {},
                        enabled = false,
                        readOnly = true,
                        label = {
                            Text(text = stringResource(R.string.dark_theme_config))
                        },
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
                        modifier = Modifier
                            .fillMaxWidth()
                            .clickable {
                                isShowingDropdownMenu = true
                            },
                    )

                    fun chooseDarkThemeConfig(
                        darkThemeConfig: DarkThemeConfig,
                    ) {
                        coroutineScope.launch {
                            setDarkThemeConfig(darkThemeConfig)
                            isShowingDropdownMenu = false
                        }
                    }

                    DropdownMenu(
                        expanded = isShowingDropdownMenu,
                        onDismissRequest = { isShowingDropdownMenu = false },
                    ) {
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.follow_system)) },
                            onClick = {
                                chooseDarkThemeConfig(DarkThemeConfig.FollowSystem)
                            },
                        )
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.dark_theme)) },
                            onClick = {
                                chooseDarkThemeConfig(DarkThemeConfig.Dark)
                            },
                        )
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.light_theme)) },
                            onClick = {
                                chooseDarkThemeConfig(DarkThemeConfig.Light)
                            },
                        )
                    }
                }
            }
        }
    }
}

@Preview
@Composable
fun DarkThemeConfigUiLoadingPreview() {
    ComposeLifeTheme {
        DarkThemeConfigUi(
            darkThemeConfigState = ResourceState.Loading,
            setDarkThemeConfig = {},
        )
    }
}

@Preview
@Composable
fun DarkThemeConfigUiLoadedPreview() {
    ComposeLifeTheme {
        DarkThemeConfigUi(
            darkThemeConfigState = ResourceState.Success(DarkThemeConfig.FollowSystem),
            setDarkThemeConfig = {},
        )
    }
}

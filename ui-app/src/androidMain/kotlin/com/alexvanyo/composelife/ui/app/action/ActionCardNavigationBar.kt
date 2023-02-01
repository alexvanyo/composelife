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

import androidx.compose.animation.core.animateDpAsState
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Edit
import androidx.compose.material.icons.filled.Settings
import androidx.compose.material.icons.filled.Speed
import androidx.compose.material.icons.outlined.Edit
import androidx.compose.material.icons.outlined.Settings
import androidx.compose.material.icons.outlined.Speed
import androidx.compose.material3.Icon
import androidx.compose.material3.NavigationBar
import androidx.compose.material3.NavigationBarItem
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.app.R

@Suppress("LongMethod")
@Composable
fun ActionCardNavigationBar(
    actionCardState: CellUniverseActionCardState,
    isElevated: Boolean,
    modifier: Modifier = Modifier,
) {
    val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

    NavigationBar(
        modifier = modifier,
        tonalElevation = elevation,
    ) {
        val speedSelected =
            actionCardState.navigationState.currentEntry.value is ActionCardNavigation.Speed
        val editSelected =
            actionCardState.navigationState.currentEntry.value is ActionCardNavigation.Edit
        val settingsSelected =
            actionCardState.navigationState.currentEntry.value is ActionCardNavigation.Settings

        NavigationBarItem(
            selected = speedSelected,
            onClick = actionCardState::onSpeedClicked,
            icon = {
                Icon(
                    if (speedSelected) {
                        Icons.Filled.Speed
                    } else {
                        Icons.Outlined.Speed
                    },
                    contentDescription = "",
                )
            },
            label = {
                Text(text = stringResource(id = R.string.speed))
            },
        )
        NavigationBarItem(
            selected = editSelected,
            onClick = actionCardState::onEditClicked,
            icon = {
                Icon(
                    if (editSelected) {
                        Icons.Filled.Edit
                    } else {
                        Icons.Outlined.Edit
                    },
                    contentDescription = "",
                )
            },
            label = {
                Text(text = stringResource(id = R.string.edit))
            },
        )
        NavigationBarItem(
            selected = settingsSelected,
            onClick = actionCardState::onSettingsClicked,
            icon = {
                Icon(
                    if (settingsSelected) {
                        Icons.Filled.Settings
                    } else {
                        Icons.Outlined.Settings
                    },
                    contentDescription = "",
                )
            },
            label = {
                Text(text = stringResource(id = R.string.settings))
            },
        )
    }
}

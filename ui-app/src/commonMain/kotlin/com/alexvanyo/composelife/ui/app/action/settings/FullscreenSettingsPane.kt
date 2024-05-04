/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.component.ListDetailPaneScaffold
import com.alexvanyo.composelife.ui.util.SharedTransitionScope

context(
    SharedTransitionScope,
    FullscreenSettingsDetailPaneInjectEntryPoint,
    FullscreenSettingsDetailPaneLocalEntryPoint
)
@Composable
fun FullscreenSettingsPane(
    listUiNavValue: ComposeLifeUiNavigation.FullscreenSettingsList,
    detailsUiNavValue: ComposeLifeUiNavigation.FullscreenSettingsDetail,
    onBackButtonPressed: () -> Unit,
    setSettingsCategory: (SettingsCategory) -> Unit,
    modifier: Modifier = Modifier,
) {
    ListDetailPaneScaffold(
        showList = listUiNavValue.isListVisible,
        showDetail = listUiNavValue.isDetailVisible,
        listContent = {
            FullscreenSettingsListPane(
                navEntryValue = listUiNavValue,
                setSettingsCategory = setSettingsCategory,
                onBackButtonPressed = onBackButtonPressed,
            )
        },
        detailContent = {
            FullscreenSettingsDetailPane(
                navEntryValue = detailsUiNavValue,
                onBackButtonPressed = onBackButtonPressed,
            )
        },
        onBackButtonPressed = onBackButtonPressed,
        modifier = modifier,
    )
}

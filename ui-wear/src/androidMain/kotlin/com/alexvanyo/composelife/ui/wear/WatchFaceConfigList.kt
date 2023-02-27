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

package com.alexvanyo.composelife.ui.wear

import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import androidx.wear.compose.foundation.lazy.AutoCenteringParams
import androidx.wear.compose.foundation.lazy.ScalingLazyColumn
import androidx.wear.compose.foundation.lazy.ScalingLazyListState
import androidx.wear.compose.foundation.rememberActiveFocusRequester
import androidx.wear.compose.material.Chip
import androidx.wear.compose.material.ChipDefaults
import androidx.wear.compose.material.CircularProgressIndicator
import androidx.wear.compose.material.Switch
import androidx.wear.compose.material.Text
import androidx.wear.compose.material.ToggleChip
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.google.android.horologist.compose.navscaffold.ExperimentalHorologistComposeLayoutApi
import com.google.android.horologist.compose.rotaryinput.rotaryWithScroll
import com.alexvanyo.composelife.resources.wear.R as resourcesWearR

@OptIn(ExperimentalHorologistComposeLayoutApi::class)
@Suppress("LongMethod")
@Composable
fun WatchFaceConfigList(
    state: WatchFaceConfigState,
    onEditColorClicked: () -> Unit,
    scalingLazyListState: ScalingLazyListState,
    modifier: Modifier = Modifier,
) {
    val focusRequester = rememberActiveFocusRequester()

    ScalingLazyColumn(
        modifier = modifier
            .rotaryWithScroll(focusRequester, scalingLazyListState),
        state = scalingLazyListState,
        autoCentering = AutoCenteringParams(itemIndex = 0)
    ) {
        item {
            Box(
                contentAlignment = Alignment.Center,
                modifier = Modifier.fillMaxWidth(),
            ) {
                val currentPreview = state.preview
                when (currentPreview) {
                    is ResourceState.Failure, ResourceState.Loading -> {
                        Box(
                            contentAlignment = Alignment.Center,
                            modifier = Modifier
                                .fillMaxWidth(0.8f)
                                .aspectRatio(1f)
                                .fillMaxHeight()
                        ) {
                            CircularProgressIndicator()
                        }
                    }
                    is ResourceState.Success -> {
                        WatchFacePreview(
                            previewImageBitmap = currentPreview.value,
                            onComplicationClicked = { id ->
                                state.openComplicationDataSourceChooser(id)
                            },
                            modifier = Modifier.fillMaxWidth(0.8f)
                        )
                    }
                }
            }
        }
        item {
            Chip(
                label = {
                    Text(text = stringResource(id = resourcesWearR.string.color))
                },
                icon = {
                    Spacer(
                        modifier = Modifier
                            .size(16.dp)
                            .background(state.color, CircleShape)
                    )
                },
                colors = ChipDefaults.secondaryChipColors(),
                onClick = onEditColorClicked,
                modifier = Modifier.fillMaxWidth()
            )
        }
        item {
            ToggleChip(
                checked = state.showComplicationsInAmbient,
                onCheckedChange = {
                    state.showComplicationsInAmbient = it
                },
                label = {
                    Text(text = stringResource(id = resourcesWearR.string.show_complications_in_ambient))
                },
                toggleControl = {
                    Switch(
                        checked = state.showComplicationsInAmbient,
                    )
                },
                modifier = Modifier.fillMaxWidth()
            )
        }
    }
}

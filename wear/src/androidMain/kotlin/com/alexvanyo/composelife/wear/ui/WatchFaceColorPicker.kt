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

package com.alexvanyo.composelife.wear.ui

import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.widthIn
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.RectangleShape
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import androidx.wear.compose.material.MaterialTheme
import com.alexvanyo.composelife.ui.util.ColorComponent
import com.alexvanyo.composelife.ui.util.WearDevicePreviews
import com.alexvanyo.composelife.ui.util.get
import com.alexvanyo.composelife.ui.util.values
import com.alexvanyo.composelife.ui.util.withComponent
import com.alexvanyo.composelife.wear.R

@Composable
fun WatchFaceColorPicker(
    color: Color,
    setColor: (Color) -> Unit,
    modifier: Modifier = Modifier,
) {
    var selectedComponent: ColorComponent.RgbIntComponent by rememberSaveable(
        stateSaver = ColorComponent.RgbIntComponent.Saver
    ) {
        mutableStateOf(ColorComponent.RgbIntComponent.Red)
    }

    Row(
        horizontalArrangement = Arrangement.Center,
        modifier = modifier
            .fillMaxSize()
            .background(color)
            .padding(12.dp)
            .background(
                MaterialTheme.colors.background,
                if (LocalConfiguration.current.isScreenRound) CircleShape else RectangleShape,
            )
            .clip(
                if (LocalConfiguration.current.isScreenRound) CircleShape else RectangleShape
            )
    ) {
        ColorComponent.RgbIntComponent.values.forEach { component ->
            key(component) {
                ColorComponentPicker(
                    isSelected = selectedComponent == component,
                    onSelected = { selectedComponent = component },
                    initialComponentValue = color.get(component),
                    setComponentValue = {
                        setColor(color.withComponent(component, it))
                    },
                    contentDescription = stringResource(
                        when (component) {
                            ColorComponent.RgbIntComponent.Red -> R.string.color_red_value
                            ColorComponent.RgbIntComponent.Green -> R.string.color_green_value
                            ColorComponent.RgbIntComponent.Blue -> R.string.color_blue_value
                        }
                    ),
                    modifier = Modifier.weight(1f, fill = false).widthIn(max = 48.dp),
                )
            }
        }
    }
}

@WearDevicePreviews
@Composable
fun WatchFaceColorPickerPreview() {
    var color by remember { mutableStateOf(Color.Cyan) }
    WatchFaceColorPicker(
        color = color,
        setColor = { color = it },
    )
}

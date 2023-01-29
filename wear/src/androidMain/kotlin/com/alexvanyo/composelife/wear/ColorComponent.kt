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

package com.alexvanyo.composelife.wear

import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.toArgb
import androidx.core.graphics.alpha
import androidx.core.graphics.blue
import androidx.core.graphics.green
import androidx.core.graphics.red
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.alexvanyo.composelife.wear.ColorComponent.RgbIntComponent
import com.livefront.sealedenum.GenSealedEnum

sealed interface ColorComponent {
    sealed interface RgbIntComponent {
        object Red : RgbIntComponent
        object Green : RgbIntComponent
        object Blue : RgbIntComponent

        @GenSealedEnum
        companion object {
            val Saver = sealedEnumSaver(sealedEnum)
        }
    }
    object Alpha : ColorComponent

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

fun Color.withComponent(component: RgbIntComponent, value: Int): Color =
    Color(
        red = if (component == RgbIntComponent.Red) value else get(RgbIntComponent.Red),
        green = if (component == RgbIntComponent.Green) value else get(RgbIntComponent.Green),
        blue = if (component == RgbIntComponent.Blue) value else get(RgbIntComponent.Blue),
        alpha = toArgb().alpha
    )

fun Color.get(component: RgbIntComponent): Int =
    toArgb().let {
        when (component) {
            RgbIntComponent.Blue -> it.blue
            RgbIntComponent.Green -> it.green
            RgbIntComponent.Red -> it.red
        }
    }

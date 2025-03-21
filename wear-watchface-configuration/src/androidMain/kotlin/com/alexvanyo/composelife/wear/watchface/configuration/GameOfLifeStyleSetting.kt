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

package com.alexvanyo.composelife.wear.watchface.configuration

import android.content.Context
import android.content.res.Resources
import androidx.compose.ui.graphics.Color
import androidx.wear.watchface.style.MutableUserStyle
import androidx.wear.watchface.style.UserStyle
import androidx.wear.watchface.style.UserStyleSchema
import androidx.wear.watchface.style.UserStyleSetting
import androidx.wear.watchface.style.WatchFaceLayer
import com.alexvanyo.composelife.resources.wear.R
import com.alexvanyo.composelife.ui.util.ColorComponent
import com.alexvanyo.composelife.ui.util.get
import com.livefront.sealedenum.GenSealedEnum

/**
 * A style setting used for the watchface configuration.
 */
sealed interface GameOfLifeStyleSetting {

    /**
     * The id for the [UserStyleSetting].
     */
    val id: UserStyleSetting.Id

    /**
     * Creates the [UserStyleSetting] using the given [resources].
     */
    fun createUserStyleSetting(resources: Resources): UserStyleSetting

    data object ColorRedValue : GameOfLifeStyleSetting {
        override val id = UserStyleSetting.Id("game_of_life_color_red_value")

        override fun createUserStyleSetting(resources: Resources): UserStyleSetting.LongRangeUserStyleSetting =
            UserStyleSetting.LongRangeUserStyleSetting.Builder(
                id = id,
                minimumValue = 0,
                maximumValue = 255,
                defaultValue = 255,
                affectsWatchFaceLayers = listOf(
                    WatchFaceLayer.BASE,
                    WatchFaceLayer.COMPLICATIONS,
                ),
                resources = resources,
                displayNameResourceId = R.string.color_red_value,
                descriptionResourceId = R.string.color_red_value_description,
            )
                .build()
    }

    data object ColorGreenValue : GameOfLifeStyleSetting {
        override val id = UserStyleSetting.Id("game_of_life_color_green_value")

        override fun createUserStyleSetting(resources: Resources): UserStyleSetting.LongRangeUserStyleSetting =
            UserStyleSetting.LongRangeUserStyleSetting.Builder(
                id = id,
                minimumValue = 0,
                maximumValue = 255,
                defaultValue = 255,
                affectsWatchFaceLayers = listOf(
                    WatchFaceLayer.BASE,
                    WatchFaceLayer.COMPLICATIONS,
                ),
                resources = resources,
                displayNameResourceId = R.string.color_green_value,
                descriptionResourceId = R.string.color_green_value_description,
            )
                .build()
    }

    data object ColorBlueValue : GameOfLifeStyleSetting {
        override val id = UserStyleSetting.Id("game_of_life_color_blue_value")

        override fun createUserStyleSetting(resources: Resources): UserStyleSetting.LongRangeUserStyleSetting =
            UserStyleSetting.LongRangeUserStyleSetting.Builder(
                id = id,
                minimumValue = 0,
                maximumValue = 255,
                defaultValue = 255,
                affectsWatchFaceLayers = listOf(
                    WatchFaceLayer.BASE,
                    WatchFaceLayer.COMPLICATIONS,
                ),
                resources = resources,
                displayNameResourceId = R.string.color_blue_value,
                descriptionResourceId = R.string.color_blue_value_description,
            )
                .build()
    }

    data object ShowComplicationsInAmbient : GameOfLifeStyleSetting {
        override val id = UserStyleSetting.Id("show_complications_in_ambient")

        override fun createUserStyleSetting(resources: Resources): UserStyleSetting.BooleanUserStyleSetting =
            UserStyleSetting.BooleanUserStyleSetting.Builder(
                id = id,
                affectsWatchFaceLayers = listOf(
                    WatchFaceLayer.COMPLICATIONS,
                ),
                defaultValue = true,
                resources = resources,
                displayNameResourceId = R.string.show_complications_in_ambient,
                descriptionResourceId = R.string.show_complications_in_ambient_description,
            )
                .build()
    }

    @GenSealedEnum
    companion object
}

/**
 * Returns the [Color] for the [UserStyle] given the [UserStyleSchema].
 *
 * The color is stored as 3 underlying [Long] settings representing the RGB color components.
 */
context(userStyleSchema: UserStyleSchema)
fun UserStyle.getGameOfLifeColor(): Color {
    val colorRedValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorRedValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting
    val colorGreenValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorGreenValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting
    val colorBlueValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorBlueValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting

    return Color(
        (
            this[colorRedValueUserSetting] as
                UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption
            ).value.toInt(),
        (
            this[colorGreenValueUserSetting] as
                UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption
            ).value.toInt(),
        (
            this[colorBlueValueUserSetting] as
                UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption
            ).value.toInt(),
    )
}

/**
 * Sets the preferred [Color] to the [MutableUserStyle] given the [UserStyleSchema].
 *
 * The color is stored as 3 underlying [Long] settings representing the RGB color components.
 */
context(userStyleSchema: UserStyleSchema)
fun MutableUserStyle.setGameOfLifeColor(color: Color) {
    val colorRedValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorRedValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting
    val colorGreenValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorGreenValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting
    val colorBlueValueUserSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ColorBlueValue.id
    } as UserStyleSetting.LongRangeUserStyleSetting

    this[colorRedValueUserSetting] =
        UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption(
            color.get(ColorComponent.RgbIntComponent.Red).toLong(),
        )
    this[colorGreenValueUserSetting] =
        UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption(
            color.get(ColorComponent.RgbIntComponent.Green).toLong(),
        )
    this[colorBlueValueUserSetting] =
        UserStyleSetting.LongRangeUserStyleSetting.LongRangeOption(
            color.get(ColorComponent.RgbIntComponent.Blue).toLong(),
        )
}

/**
 * Gets the preferred setting to show complications in ambient from the [UserStyle] given the [UserStyleSchema].
 */
context(userStyleSchema: UserStyleSchema)
fun UserStyle.getShowComplicationsInAmbient(): Boolean {
    val showComplicationsInAmbientSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ShowComplicationsInAmbient.id
    } as UserStyleSetting.BooleanUserStyleSetting
    return (this[showComplicationsInAmbientSetting] as UserStyleSetting.BooleanUserStyleSetting.BooleanOption).value
}

/**
 * Sets the preferred setting to show complications in ambient to the [MutableUserStyle] given the [UserStyleSchema].
 */
context(userStyleSchema: UserStyleSchema)
fun MutableUserStyle.setShowComplicationsInAmbient(value: Boolean) {
    val showComplicationsInAmbientSetting = userStyleSchema.rootUserStyleSettings.find {
        it.id == GameOfLifeStyleSetting.ShowComplicationsInAmbient.id
    } as UserStyleSetting.BooleanUserStyleSetting
    this[showComplicationsInAmbientSetting] = if (value) {
        UserStyleSetting.BooleanUserStyleSetting.BooleanOption.TRUE
    } else {
        UserStyleSetting.BooleanUserStyleSetting.BooleanOption.FALSE
    }
}

/**
 * Creates the [UserStyleSchema] with the defined settings.
 */
fun createGameOfLifeStyleSchema(context: Context): UserStyleSchema =
    UserStyleSchema(GameOfLifeStyleSetting.values.map { it.createUserStyleSetting(context.resources) })

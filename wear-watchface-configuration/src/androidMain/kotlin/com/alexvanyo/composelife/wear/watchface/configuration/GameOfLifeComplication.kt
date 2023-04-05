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
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.graphics.toAndroidRectF
import androidx.wear.watchface.CanvasComplicationFactory
import androidx.wear.watchface.ComplicationSlot
import androidx.wear.watchface.ComplicationSlotsManager
import androidx.wear.watchface.complications.ComplicationSlotBounds
import androidx.wear.watchface.complications.DefaultComplicationDataSourcePolicy
import androidx.wear.watchface.complications.SystemDataSources
import androidx.wear.watchface.complications.data.ComplicationType
import androidx.wear.watchface.complications.rendering.CanvasComplicationDrawable
import androidx.wear.watchface.complications.rendering.ComplicationDrawable
import androidx.wear.watchface.style.CurrentUserStyleRepository
import com.livefront.sealedenum.GenSealedEnum

sealed class GameOfLifeComplication(
    val id: Int,
    val supportedTypes: List<ComplicationType> = listOf(
        ComplicationType.EMPTY,
        ComplicationType.NO_DATA,
        ComplicationType.RANGED_VALUE,
        ComplicationType.MONOCHROMATIC_IMAGE,
        ComplicationType.SHORT_TEXT,
        ComplicationType.SMALL_IMAGE,
    ),
    val defaultDataSourcePolicy: DefaultComplicationDataSourcePolicy,
    val rawBounds: Rect,
) {
    val bounds: ComplicationSlotBounds = ComplicationSlotBounds(
        rawBounds.toAndroidRectF(),
    )

    object TopLeft : GameOfLifeComplication(
        id = 0,
        defaultDataSourcePolicy = DefaultComplicationDataSourcePolicy(
            SystemDataSources.DATA_SOURCE_DATE,
            ComplicationType.SHORT_TEXT,
        ),
        rawBounds = Rect(
            0.25f,
            0.10f,
            0.45f,
            0.30f,
        ),
    )

    object TopRight : GameOfLifeComplication(
        id = 1,
        defaultDataSourcePolicy = DefaultComplicationDataSourcePolicy(
            SystemDataSources.DATA_SOURCE_DAY_OF_WEEK,
            ComplicationType.SHORT_TEXT,
        ),
        rawBounds = Rect(
            0.55f,
            0.1f,
            0.75f,
            0.3f,
        ),
    )

    object BottomLeft : GameOfLifeComplication(
        id = 2,
        defaultDataSourcePolicy = DefaultComplicationDataSourcePolicy(
            SystemDataSources.DATA_SOURCE_WATCH_BATTERY,
            ComplicationType.RANGED_VALUE,
        ),
        rawBounds = Rect(
            0.25f,
            0.7f,
            0.45f,
            0.9f,
        ),
    )

    object BottomRight : GameOfLifeComplication(
        id = 3,
        defaultDataSourcePolicy = DefaultComplicationDataSourcePolicy(
            SystemDataSources.DATA_SOURCE_UNREAD_NOTIFICATION_COUNT,
            ComplicationType.MONOCHROMATIC_IMAGE,
        ),
        rawBounds = Rect(
            0.55f,
            0.7f,
            0.75f,
            0.9f,
        ),
    )

    @GenSealedEnum
    companion object
}

fun createGameOfLifeComplicationSlotsManager(
    context: Context,
    currentUserStyleRepository: CurrentUserStyleRepository,
): ComplicationSlotsManager {
    val canvasComplicationFactory = CanvasComplicationFactory { watchState, invalidateCallback ->
        CanvasComplicationDrawable(
            drawable = checkNotNull(ComplicationDrawable.getDrawable(context, R.drawable.complication_style)),
            watchState = watchState,
            invalidateCallback = invalidateCallback,
        )
    }

    return ComplicationSlotsManager(
        GameOfLifeComplication.values.map { gameOfLifeComplication ->
            ComplicationSlot
                .createRoundRectComplicationSlotBuilder(
                    id = gameOfLifeComplication.id,
                    canvasComplicationFactory = canvasComplicationFactory,
                    supportedTypes = gameOfLifeComplication.supportedTypes,
                    defaultDataSourcePolicy = gameOfLifeComplication.defaultDataSourcePolicy,
                    bounds = gameOfLifeComplication.bounds,
                )
                .build()
        },
        currentUserStyleRepository,
    )
}

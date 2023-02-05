/*
 * Copyright 2020 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


package com.alexvanyo.composelife.wear.watchface

import android.content.Context
import android.view.SurfaceHolder
import androidx.wear.watchface.ComplicationSlotsManager
import androidx.wear.watchface.WatchFace
import androidx.wear.watchface.WatchFaceService
import androidx.wear.watchface.WatchState
import androidx.wear.watchface.style.CurrentUserStyleRepository
import kotlinx.datetime.TimeZone
import kotlinx.datetime.toJavaZoneId

/** A simple OpenGL test watch face for integration tests. */
internal class DelegatingWatchFaceService(
    context: Context,
    private val surfaceHolder: SurfaceHolder,
) : WatchFaceService() {

    val delegate = object : GameOfLifeWatchFaceService() {
        init {
            attachBaseContext(context)
        }
    }

    init {
        attachBaseContext(context)
    }

    override fun createUserStyleSchema() = delegate.createUserStyleSchema()

    override fun createComplicationSlotsManager(
        currentUserStyleRepository: CurrentUserStyleRepository
    ) = delegate.createComplicationSlotsManager(currentUserStyleRepository)

    override suspend fun createWatchFace(
        surfaceHolder: SurfaceHolder,
        watchState: WatchState,
        complicationSlotsManager: ComplicationSlotsManager,
        currentUserStyleRepository: CurrentUserStyleRepository
    ): WatchFace = delegate.createWatchFace(
        surfaceHolder,
        watchState,
        complicationSlotsManager,
        currentUserStyleRepository
    )

    override fun getWallpaperSurfaceHolderOverride() = surfaceHolder

    override fun getSystemTimeProvider() = object : SystemTimeProvider {
        override fun getSystemTimeMillis() = 1675577751744L
        override fun getSystemTimeZoneId() = TimeZone.UTC.toJavaZoneId()
    }
}

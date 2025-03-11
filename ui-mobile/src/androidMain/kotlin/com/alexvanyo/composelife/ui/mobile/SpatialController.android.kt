/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.mobile

import android.os.Build
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.xr.compose.platform.LocalHasXrSpatialFeature
import androidx.xr.compose.platform.LocalSession
import androidx.xr.compose.platform.LocalSpatialCapabilities

@Composable
actual fun rememberSpatialController(): SpatialController =
    if (Build.VERSION.SDK_INT >= 34) {
        val hasXrSpatialFeature = LocalHasXrSpatialFeature.current
        val spatialCapabilities = LocalSpatialCapabilities.current
        val xrSession = LocalSession.current

        remember(hasXrSpatialFeature, spatialCapabilities, xrSession) {
            object : SpatialController {
                override val hasXrSpatialFeature: Boolean get() = hasXrSpatialFeature
                override val isSpatialUiEnabled: Boolean get() = spatialCapabilities.isSpatialUiEnabled
                override var isFullSpaceMode: Boolean
                    get() = isSpatialUiEnabled
                    set(value) {
                        if (value) {
                            xrSession?.spatialEnvironment?.requestFullSpaceMode()
                        } else {
                            xrSession?.spatialEnvironment?.requestHomeSpaceMode()
                        }
                    }
            }
        }
    } else {
        remember {
            object : SpatialController {
                override val hasXrSpatialFeature: Boolean = false
                override val isSpatialUiEnabled: Boolean = false
                override var isFullSpaceMode: Boolean
                    get() = false
                    set(value) = Unit
            }
        }
    }

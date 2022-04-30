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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.ui.platform.LocalInspectionMode
import app.cash.paparazzi.DeviceConfig
import app.cash.paparazzi.Paparazzi
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.android.resources.NightMode
import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import org.junit.Rule
import org.junit.runner.RunWith

private val globalPaparazzi = Paparazzi(
    maxPercentDifference = 0.0,
)

@RunWith(TestParameterInjector::class)
@Suppress("UnnecessaryAbstractClass")
abstract class BasePaparazziTest {

    enum class BaseDeviceConfig(
        val deviceConfig: DeviceConfig,
    ) {
        NEXUS_5(DeviceConfig.NEXUS_5),
        PIXEL_5(DeviceConfig.PIXEL_5),
        PIXEL_C(DeviceConfig.PIXEL_C),
    }

    @TestParameter
    lateinit var baseDeviceConfig: BaseDeviceConfig

    @TestParameter
    lateinit var nightMode: NightMode

    @get:Rule
    val paparazzi = globalPaparazzi

    private val deviceConfig get() = baseDeviceConfig.deviceConfig.copy(
        nightMode = nightMode,
        softButtons = false,
    )

    fun snapshot(composable: @Composable () -> Unit) {
        paparazzi.snapshot(deviceConfig = deviceConfig) {
            CompositionLocalProvider(LocalInspectionMode provides true) {
                ComposeLifeTheme(darkTheme = nightMode == NightMode.NIGHT) {
                    Box {
                        composable()
                    }
                }
            }
        }
    }
}

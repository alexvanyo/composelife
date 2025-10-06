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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.isSystemInDarkTheme
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import com.airbnb.android.showkase.models.Showkase
import com.alexvanyo.composelife.roborazzishowkasescreenshottest.BaseRoborazziParameterizationProvider
import com.alexvanyo.composelife.roborazzishowkasescreenshottest.BaseRoborazziTest
import com.alexvanyo.composelife.roborazzishowkasescreenshottest.RoborazziParameterization
import com.alexvanyo.composelife.roborazzishowkasescreenshottest.SingleRoborazziParameterization
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.google.testing.junit.testparameterinjector.TestParameter

class RoborazziTest(
    @TestParameter(valuesProvider = Provider::class)
    roborazziParameterization: RoborazziParameterization,
) : BaseRoborazziTest(
    roborazziParameterization = roborazziParameterization,
    contentWrapper = { content ->
        ComposeLifeTheme(
            darkTheme = isSystemInDarkTheme(),
            content = content,
        )
    },
) {
    override val parameterizations = RoborazziTest.parameterizations

    companion object {
        val parameterizations = Showkase.getMetadata().componentList
            .filter { it.componentKey.startsWith("com.alexvanyo.composelife.ui.settings") }
            .flatMap { showkaseBrowserComponent ->
                listOf(
                    DpSize(320.dp, 533.dp), // Nexus One portrait
                    DpSize(393.dp, 851.dp), // Pixel 5 portrait
                    DpSize(1200.dp, 800.dp), // Pixel Tablet landscape
                ).flatMap { size ->
                    listOf(false, true).flatMap { darkTheme ->
                        listOf(1.0f, 1.5f).map { fontScale ->
                            SingleRoborazziParameterization(
                                showkaseBrowserComponent = showkaseBrowserComponent,
                                size = size,
                                darkTheme = darkTheme,
                                isScreenRound = false,
                                fontScale = fontScale,
                            )
                        }
                    }
                }
            }

        class Provider : BaseRoborazziParameterizationProvider(parameterizations)
    }
}

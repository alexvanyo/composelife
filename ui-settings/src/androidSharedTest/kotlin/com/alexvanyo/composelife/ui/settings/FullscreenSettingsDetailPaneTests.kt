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

import android.os.Build
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.ForcedSize
import androidx.compose.ui.test.WindowInsets
import androidx.compose.ui.test.assertIsFocused
import androidx.compose.ui.test.getBoundsInRoot
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performScrollTo
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.unit.DpRect
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.roundToIntRect
import androidx.core.graphics.Insets
import androidx.core.view.WindowInsetsCompat
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.settings.resources.CornerFractionLabel
import com.alexvanyo.composelife.ui.settings.resources.Strings
import org.junit.Assume.assumeTrue
import kotlin.test.Test
import kotlin.test.assertIs
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
class FullscreenSettingsDetailPaneTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent.Companion::createComponent,
) {
    private val entryPoint: TestComposeLifeApplicationEntryPoint get() = applicationComponent.kmpGetEntryPoint()

    private val composeLifePreferences get() = entryPoint.composeLifePreferences

    @Test
    fun visual_settings_category_keeps_scroll_position_with_ime() = runUiTest { uiComponent, composeUiTest ->
        assumeTrue(Build.VERSION.SDK_INT >= 30)
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.kmpGetEntryPoint()

        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        lateinit var resolver: (ParameterizedString) -> String

        var imeBottom by mutableStateOf(0.dp)

        composeUiTest.setContent {
            resolver = parameterizedStringResolver()
            with(fullscreenSettingsDetailPaneInjectEntryPoint) {
                with(
                    object : FullscreenSettingsDetailPaneLocalEntryPoint {
                        override val preferences get() =
                            assertIs<ResourceState.Success<LoadedComposeLifePreferences>>(
                                composeLifePreferences.loadedPreferencesState,
                            ).value
                    },
                ) {
                    DeviceConfigurationOverride(
                        DeviceConfigurationOverride.ForcedSize(DpSize(400.dp, 1200.dp)),
                    ) {
                        DeviceConfigurationOverride(
                            DeviceConfigurationOverride.WindowInsets(
                                WindowInsetsCompat.Builder()
                                    .setInsets(
                                        WindowInsetsCompat.Type.ime(),
                                        with(LocalDensity.current) {
                                            DpRect(0.dp, 0.dp, 0.dp, imeBottom).toRect()
                                        }.roundToIntRect().toAndroidXInsets(),
                                    )
                                    .build(),
                            ),
                        ) {
                            FullscreenSettingsDetailPane(
                                fullscreenSettingsDetailPaneState = object : FullscreenSettingsDetailPaneState {
                                    override val settingsCategory = SettingsCategory.Visual
                                    override val settingToScrollTo = null
                                    override fun onFinishedScrollingToSetting() = Unit

                                    override val isListVisible: Boolean = false
                                    override val isDetailVisible: Boolean = true
                                },
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        composeUiTest.onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.CornerFractionLabel)),
        )
            .performScrollTo()
            .performClick()

        imeBottom = 1000.dp

        composeUiTest.waitForIdle()

        val boundsInRoot = composeUiTest.onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.CornerFractionLabel)),
        )
            .assertIsFocused()
            .getBoundsInRoot()

        assertTrue(boundsInRoot.bottom <= 250.dp)
    }
}

private fun IntRect.toAndroidXInsets(): Insets =
    Insets.of(top, left, right, bottom)

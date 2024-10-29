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

package com.alexvanyo.composelife.ui.app.action.settings

import android.os.Build
import android.view.WindowInsets
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.platform.AbstractComposeView
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.ForcedSize
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
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.view.WindowInsetsCompat
import androidx.core.view.children
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.firstSuccess
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.ComposeLifeNavigation
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.resources.CornerFractionLabel
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import org.junit.Assume.assumeTrue
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertIs
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class FullscreenSettingsDetailPaneTests :
    BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
        TestComposeLifeApplicationComponent::createComponent,
        TestComposeLifeUiComponent::createComponent,
    ) {
    private val composeLifePreferences get() = applicationComponent.composeLifePreferences

    @Test
    fun visual_settings_category_keeps_scroll_position_with_ime() = runUiTest {
        assumeTrue(Build.VERSION.SDK_INT >= 30)
        val fullscreenSettingsDetailPaneInjectEntryPoint: FullscreenSettingsDetailPaneInjectEntryPoint =
            uiComponent.entryPoint

        snapshotFlow { composeLifePreferences.loadedPreferencesState }.firstSuccess()

        lateinit var resolver: (ParameterizedString) -> String

        var imeBottom by mutableStateOf(0.dp)

        setContent {
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
                                navEntryValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                                    nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                                        settingsCategory = SettingsCategory.Visual,
                                        initialSettingToScrollTo = null,
                                    ),
                                    listDetailInfo = object : ListDetailInfo {
                                        override val isListVisible: Boolean = false
                                        override val isDetailVisible: Boolean = true
                                    },
                                ),
                                onBackButtonPressed = {},
                            )
                        }
                    }
                }
            }
        }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.CornerFractionLabel)),
        )
            .performScrollTo()
            .performClick()

        imeBottom = 1000.dp

        waitForIdle()

        val boundsInRoot = onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.CornerFractionLabel)),
        )
            .assertIsFocused()
            .getBoundsInRoot()

        assertTrue(boundsInRoot.bottom <= 250.dp)
    }
}

private fun IntRect.toAndroidXInsets(): androidx.core.graphics.Insets =
    androidx.core.graphics.Insets.of(top, left, right, bottom)

fun DeviceConfigurationOverride.Companion.WindowInsets(
    windowInsets: WindowInsetsCompat,
): DeviceConfigurationOverride = DeviceConfigurationOverride { contentUnderTest ->
    val currentContentUnderTest by rememberUpdatedState(contentUnderTest)
    val currentWindowInsets by rememberUpdatedState(windowInsets)
    AndroidView(
        factory = { context ->
            object : AbstractComposeView(context) {
                @Composable
                override fun Content() {
                    currentContentUnderTest()
                }

                override fun dispatchApplyWindowInsets(insets: WindowInsets): WindowInsets {
                    children.forEach {
                        it.dispatchApplyWindowInsets(
                            WindowInsets(currentWindowInsets.toWindowInsets()),
                        )
                    }
                    return WindowInsetsCompat.CONSUMED.toWindowInsets()!!
                }

                /**
                 * Deprecated, but intercept the `requestApplyInsets` call via the deprecated
                 * method.
                 */
                @Deprecated("Deprecated in Java")
                override fun requestFitSystemWindows() {
                    dispatchApplyWindowInsets(WindowInsets(currentWindowInsets.toWindowInsets()!!))
                }
            }
        },
        update = { with(currentWindowInsets) { it.requestApplyInsets() } },
    )
}

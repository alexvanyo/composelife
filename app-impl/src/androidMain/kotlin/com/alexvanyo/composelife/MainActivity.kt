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

package com.alexvanyo.composelife

import android.content.Context
import android.os.Build
import android.os.Bundle
import android.view.ViewGroup
import android.view.WindowInsetsController
import androidx.activity.compose.setContent
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.material3.adaptive.currentWindowAdaptiveInfoV2
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.platform.ComposeView
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.platform.WindowInfo
import androidx.core.splashscreen.SplashScreen.Companion.installSplashScreen
import androidx.core.view.WindowCompat
import androidx.core.view.WindowInsetsControllerCompat
import androidx.lifecycle.LifecycleOwner
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUi
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.alexvanyo.composelife.ui.util.ProvideLocalWindowInsetsHolder
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.GraphExtension
import dev.zacsweers.metro.Provides
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope

interface MainActivityUiGraphFactoryOwner {
    val mainActivityUiGraphFactory: MainActivityUiGraph.Factory
}

@GraphExtension(UiScope::class)
interface MainActivityUiGraph :
    UiGraph,
    ComposeLifePreferencesProvider {
    val composeLifeAppUi: ComposeLifeAppUi

    @ForScope(UiScope::class)
    val uiUpdatables: Set<Updatable>

    @ContributesTo(AppScope::class)
    @GraphExtension.Factory
    fun interface Factory {
        fun create(@Provides uiGraphArguments: UiGraphArguments): MainActivityUiGraph
    }
}

class MainActivity : AppCompatActivity() {

    private val composeView: ComposeView get() =
        (findViewById<ViewGroup>(android.R.id.content).getChildAt(0) as ComposeView)

    private var isPreferencesLoaded by mutableStateOf(false)

    @Suppress("LongMethod")
    override fun onCreate(savedInstanceState: Bundle?) {
        val splashScreen = installSplashScreen()
        super.onCreate(savedInstanceState)

        val mainActivityUiGraphFactory =
            (application as MainActivityUiGraphFactoryOwner).mainActivityUiGraphFactory

        // Keep the splash screen on screen until we've loaded preferences
        splashScreen.setKeepOnScreenCondition { !isPreferencesLoaded }

        WindowCompat.enableEdgeToEdge(window)
        with(WindowInsetsControllerCompat(window, window.decorView)) {
            systemBarsBehavior =
                WindowInsetsControllerCompat.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE
        }
        if (Build.VERSION.SDK_INT >= 35) {
            window.insetsController?.setSystemBarsAppearance(
                WindowInsetsController.APPEARANCE_TRANSPARENT_CAPTION_BAR_BACKGROUND,
                WindowInsetsController.APPEARANCE_TRANSPARENT_CAPTION_BAR_BACKGROUND,
            )
        }

        setContent {
            val windowInfo = LocalWindowInfo.current
            val uiGraph = remember {
                mainActivityUiGraphFactory.create(
                    object : UiGraphArguments {
                        override val activity: AppCompatActivity = this@MainActivity
                        override val uiContext: Context = activity
                        override val windowInfo: WindowInfo = windowInfo
                        override val uiLifecycleOwner: LifecycleOwner = activity
                    },
                ).also {
                    isPreferencesLoaded =
                        it.composeLifePreferences.loadedPreferencesState.isSuccess()
                }
            }
            DisposableEffect(uiGraph) {
                onDispose {
                    uiGraph.close()
                }
            }
            val uiUpdatables = uiGraph.uiUpdatables

            LaunchedEffect(uiGraph) {
                isPreferencesLoaded =
                    snapshotFlow { uiGraph.composeLifePreferences.loadedPreferencesState.isSuccess() }
                        .first { it }
            }

            LaunchedEffect(uiUpdatables) {
                supervisorScope {
                    uiUpdatables.forEach { updatable ->
                        launch {
                            updatable.update()
                        }
                    }
                }
            }

            ProvideLocalWindowInsetsHolder {
                context(uiGraph) {
                    val darkTheme = shouldUseDarkTheme()
                    DisposableEffect(darkTheme) {
                        val insetsController = WindowInsetsControllerCompat(window, window.decorView)
                        insetsController.isAppearanceLightStatusBars = !darkTheme
                        insetsController.isAppearanceLightNavigationBars = !darkTheme
                        if (Build.VERSION.SDK_INT >= 35) {
                            window.insetsController?.setSystemBarsAppearance(
                                if (darkTheme) {
                                    0
                                } else {
                                    WindowInsetsController.APPEARANCE_LIGHT_CAPTION_BARS
                                },
                                WindowInsetsController.APPEARANCE_LIGHT_CAPTION_BARS,
                            )
                        }
                        onDispose {}
                    }

                    ComposeLifeTheme(darkTheme) {
                        context(uiGraph.composeLifeAppUi) {
                            ComposeLifeAppUi(
                                windowSizeClass = currentWindowAdaptiveInfoV2().windowSizeClass,
                                windowSize = LocalWindowInfo.current.containerDpSize,
                            )
                        }
                    }
                }
            }
        }
        composeView.consumeWindowInsets = false
    }
}

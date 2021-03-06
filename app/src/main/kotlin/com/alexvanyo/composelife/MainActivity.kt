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

import android.animation.ObjectAnimator
import android.os.Bundle
import android.view.View
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.calculateWindowSizeClass
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.graphics.Color
import androidx.core.animation.doOnEnd
import androidx.core.splashscreen.SplashScreen.Companion.installSplashScreen
import androidx.core.view.WindowCompat
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.ui.ComposeLifeApp
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.google.accompanist.systemuicontroller.rememberSystemUiController
import dagger.hilt.EntryPoints
import dagger.hilt.android.AndroidEntryPoint

@AndroidEntryPoint(ComponentActivity::class)
class MainActivity : Hilt_MainActivity() {

    override fun onCreate(savedInstanceState: Bundle?) {
        val splashScreen = installSplashScreen()
        super.onCreate(savedInstanceState)

        val mainActivityEntryPoint = EntryPoints.get(this, MainActivityEntryPoint::class.java)

        // Keep the splash screen on screen until we've determine the theme
        splashScreen.setKeepOnScreenCondition {
            !mainActivityEntryPoint.composeLifePreferences.darkThemeConfigState.isSuccess()
        }

        // The splash screen library internally sets the system bars color
        // When the animation is done, poke this state to ensure we set the right ones
        var setSystemBarsColorTick by mutableStateOf(0)

        splashScreen.setOnExitAnimationListener { viewProvider ->
            ObjectAnimator.ofFloat(
                viewProvider.view,
                View.ALPHA,
                1f,
                0f,
            ).apply {
                duration = 250
                doOnEnd {
                    setSystemBarsColorTick++
                    viewProvider.remove()
                }
                start()
            }
        }

        WindowCompat.setDecorFitsSystemWindows(window, false)

        setContent {
            with(mainActivityEntryPoint) {
                ComposeLifeTheme {
                    val useDarkIcons = ComposeLifeTheme.isLight
                    val systemUiController = rememberSystemUiController()

                    LaunchedEffect(systemUiController, useDarkIcons, setSystemBarsColorTick) {
                        systemUiController.setSystemBarsColor(
                            color = Color.Transparent,
                            darkIcons = useDarkIcons,
                        )
                    }

                    @OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
                    ComposeLifeApp(calculateWindowSizeClass(this@MainActivity))
                }
            }
        }
    }
}

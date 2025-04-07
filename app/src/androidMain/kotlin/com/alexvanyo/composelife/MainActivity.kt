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

import android.app.Activity
import android.os.Build
import android.os.Bundle
import android.view.WindowManager
import androidx.activity.ComponentActivity
import androidx.activity.SystemBarStyle
import androidx.activity.compose.setContent
import androidx.activity.enableEdgeToEdge
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.DeferredTargetAnimation
import androidx.compose.animation.core.ExperimentalAnimatableApi
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.adaptive.currentWindowAdaptiveInfo
import androidx.compose.material3.adaptive.currentWindowSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionContext
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.LookaheadScope
import androidx.compose.ui.layout.layout
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import androidx.core.content.ContextCompat
import androidx.core.splashscreen.SplashScreen.Companion.installSplashScreen
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.scopes.ApplicationComponentOwner
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.scopes.UiComponentOwner
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.app.ComposeLifeAppInjectEntryPoint
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.continuityRetainedStateRegistry
import kotlinx.coroutines.launch
import kotlin.math.PI
import kotlin.math.cos
import kotlin.math.roundToInt
import kotlin.math.sin

@EntryPoint(UiScope::class)
interface MainActivityInjectEntryPoint :
    ComposeLifePreferencesProvider,
    ComposeLifeAppInjectEntryPoint

class MainActivity : AppCompatActivity(), UiComponentOwner {

    override lateinit var uiComponent: UiComponent

    @Suppress("DEPRECATION")
    override fun onCreate(savedInstanceState: Bundle?) {
        val splashScreen = installSplashScreen()
        super.onCreate(savedInstanceState)

        val application = application as ApplicationComponentOwner
        uiComponent = application.uiComponentFactory(
            object : UiComponentArguments {
                override val activity: Activity = this@MainActivity
            },
        )
        val mainActivityEntryPoint = uiComponent.getEntryPoint<MainActivityInjectEntryPoint>()

        // Keep the splash screen on screen until we've loaded preferences
        splashScreen.setKeepOnScreenCondition {
            !mainActivityEntryPoint.composeLifePreferences.loadedPreferencesState.isSuccess()
        }

        enableEdgeToEdge()
        WindowInsetsControllerCompat(window, window.decorView).systemBarsBehavior =
            WindowInsetsControllerCompat.BEHAVIOR_SHOW_TRANSIENT_BARS_BY_SWIPE

        window.attributes = window.attributes.apply {
            rotationAnimation =
                if (Build.VERSION.SDK_INT >= 26) {
                    WindowManager.LayoutParams.ROTATION_ANIMATION_SEAMLESS
                } else {
                    WindowManager.LayoutParams.ROTATION_ANIMATION_JUMPCUT
                }
        }

        setFancyContent {
            CompositionLocalProvider(LocalRetainedStateRegistry provides continuityRetainedStateRegistry()) {
                with(mainActivityEntryPoint) {
                    val darkTheme = shouldUseDarkTheme()
                    DisposableEffect(darkTheme) {
                        enableEdgeToEdge(
                            statusBarStyle = SystemBarStyle.auto(
                                android.graphics.Color.TRANSPARENT,
                                android.graphics.Color.TRANSPARENT,
                            ) { darkTheme },
                            navigationBarStyle = SystemBarStyle.auto(
                                lightScrim,
                                darkScrim,
                            ) { darkTheme },
                        )
                        onDispose {}
                    }

                    ComposeLifeTheme(darkTheme) {
                        ComposeLifeApp(
                            windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                            windowSize = with(LocalDensity.current) { currentWindowSize().toSize().toDpSize() },
                        )
                    }
                }
            }
        }
    }
}

/**
* The default light scrim, as defined by androidx and the platform:
* https://cs.android.com/androidx/platform/frameworks/support/+/androidx-main:activity/activity/src/main/java/androidx/activity/EdgeToEdge.kt;l=35-38;drc=27e7d52e8604a080133e8b842db10c89b4482598
*/
private val lightScrim = android.graphics.Color.argb(0xe6, 0xFF, 0xFF, 0xFF)

/**
 * The default dark scrim, as defined by androidx and the platform:
 * https://cs.android.com/androidx/platform/frameworks/support/+/androidx-main:activity/activity/src/main/java/androidx/activity/EdgeToEdge.kt;l=40-44;drc=27e7d52e8604a080133e8b842db10c89b4482598
 */
private val darkScrim = android.graphics.Color.argb(0x80, 0x1b, 0x1b, 0x1b)

@OptIn(ExperimentalAnimatableApi::class)
fun ComponentActivity.setFancyContent(
    parent: CompositionContext? = null,
    content: @Composable () -> Unit
) = setContent(parent) {
    val context = LocalContext.current
    val rotation = remember(
        context,
        LocalConfiguration.current.screenWidthDp,
        LocalConfiguration.current.screenHeightDp
    ) {
        ContextCompat.getDisplayOrDefault(context).rotation
    }
    val scope = rememberCoroutineScope()
    var orientationTarget by remember { mutableIntStateOf(rotation) }
    val anim = remember { Animatable(rotation * 90f) }
    val animSize = remember { DeferredTargetAnimation(Size.VectorConverter) }
    val coroutineScope = rememberCoroutineScope()
    var lookaheadSize by remember { mutableStateOf(IntSize.Zero) }
    var size by remember { mutableStateOf(Size.Zero) }
    LookaheadScope {
        Box(
            Modifier
                .graphicsLayer {
                    val delta = (rotation - orientationTarget + 4) % 4
                    if (delta != 0) {
                        if (delta == 3) {
                            orientationTarget -= 1
                        } else
                            orientationTarget += delta
                        scope.launch {
                            // Rotation animation looks best when resizing is no slower than
                            // rotation.
                            anim.animateTo(
                                orientationTarget * 90f,
                                animationSpec = spring(stiffness = Spring.StiffnessMediumLow)
                            )
                        }
                    }
                    rotationZ = (anim.value - rotation * 90f).let {
                        if (it < -180f)
                            it + 360f
                        else if (it > 180f) it - 360f
                        else it
                    }
                    val r = rotationZ * PI / 180f
                    if (rotationZ != 0f) {
                        // Rotate around the center of the screen
                        translationY = (this.size.height - size.height * cos(r) - size.width * sin(r)).toFloat() / 2f
                        translationX = (this.size.width + size.height * sin(r) - size.width * cos(r)).toFloat() / 2f
                    }
                    // First version of the rotation algorithm
//                        if (rotationZ > 0f) {
//                            val rSquared =
//                                (size.width * size.width + size.height * size.height) / 4f
//                            translationX = size.width * rotationZ / 90f
//                            translationY =
//                                -sqrt(rSquared - (translationX - size.width / 2) *
//                                (translationX - size.width / 2)) + size.height / 2f
//                        } else if (rotationZ < 0f) {
//                            val rSquared =
//                                (size.width * size.width + size.height * size.height) / 4f
//                            translationY = -size.height * rotationZ / 90f
//                            translationX =
//                                -sqrt(rSquared - (translationY - size.height / 2) *
//                                (translationY - size.height / 2)) + size.width / 2f
//                        }
                    transformOrigin = TransformOrigin(0f, 0f)
                }
                .layout { measurable, constraints ->
                    if (isLookingAhead) {
                        measurable
                            .measure(constraints)
                            .run {
                                lookaheadSize = IntSize(width, height)
                                layout(width, height) {
                                    place(0, 0)
                                }
                            }
                    } else {
                        size = animSize.updateTarget(
                            IntSize(constraints.maxWidth, constraints.maxHeight).toSize(),
                            coroutineScope,
                            animationSpec = spring(
                                stiffness = Spring.StiffnessMediumLow,
                                visibilityThreshold = Size(1f, 1f),
                            )
                        )
                        measurable
                            .measure(
                                constraints.copy(
                                    maxWidth = size.width.roundToInt(),
                                    maxHeight = size.height.roundToInt(),
                                )
                            )
                            .run {
                                layout(lookaheadSize.width, lookaheadSize.height) {
                                    place(0, 0)
                                }
                            }
                    }
                }
                .fillMaxSize()
        ) {
            content()
        }
    }
}

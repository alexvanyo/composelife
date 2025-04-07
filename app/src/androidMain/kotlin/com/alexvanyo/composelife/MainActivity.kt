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
import android.graphics.Color
import android.hardware.display.DisplayManager
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.view.ViewGroup
import android.view.WindowManager
import androidx.activity.ComponentActivity
import androidx.activity.SystemBarStyle
import androidx.activity.compose.setContent
import androidx.activity.enableEdgeToEdge
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.ExperimentalAnimatableApi
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.material3.adaptive.currentWindowAdaptiveInfo
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionContext
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.LookaheadScope
import androidx.compose.ui.platform.ComposeView
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.core.content.ContextCompat
import androidx.core.content.getSystemService
import androidx.core.splashscreen.SplashScreen.Companion.installSplashScreen
import androidx.core.view.WindowInsetsControllerCompat
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.scopes.ApplicationGraphOwner
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiGraphArguments
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.app.ComposeLifeApp
import com.alexvanyo.composelife.ui.app.ComposeLifeAppUiCtx
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.shouldUseDarkTheme
import com.alexvanyo.composelife.ui.util.ProvideLocalWindowInsetsHolder
import com.alexvanyo.composelife.ui.util.animateContentSize
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope
import kotlin.math.abs
import kotlin.math.floor

@ContributesTo(UiScope::class)
interface MainActivityInjectCtx : ComposeLifePreferencesProvider {
    val composeLifeAppUiCtx: ComposeLifeAppUiCtx

    @ForScope(UiScope::class)
    val uiUpdatables: Set<Updatable>
}

// TODO: Replace with asContribution()
internal val UiGraph.mainActivityInjectCtx: MainActivityInjectCtx get() =
    this as MainActivityInjectCtx

class MainActivity : AppCompatActivity() {

    private val composeView: ComposeView get() =
        (findViewById<ViewGroup>(android.R.id.content).getChildAt(0) as ComposeView)

    @Suppress("LongMethod")
    override fun onCreate(savedInstanceState: Bundle?) {
        val splashScreen = installSplashScreen()
        super.onCreate(savedInstanceState)

        val application = application as ApplicationGraphOwner
        val uiGraph = (application.applicationGraph as UiGraph.Factory).create(
            object : UiGraphArguments {
                override val activity: AppCompatActivity = this@MainActivity
                override val uiContext: Context = activity
            },
        )
        val mainActivityCtx = uiGraph.mainActivityInjectCtx
        val uiUpdatables = mainActivityCtx.uiUpdatables

        // Keep the splash screen on screen until we've loaded preferences
        splashScreen.setKeepOnScreenCondition {
            !mainActivityCtx.composeLifePreferences.loadedPreferencesState.isSuccess()
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
                with(mainActivityCtx) {
                    val darkTheme = shouldUseDarkTheme()
                    DisposableEffect(darkTheme) {
                        enableEdgeToEdge(
                            statusBarStyle = SystemBarStyle.auto(
                                Color.TRANSPARENT,
                                Color.TRANSPARENT,
                            ) { darkTheme },
                            navigationBarStyle = SystemBarStyle.auto(
                                lightScrim,
                                darkScrim,
                            ) { darkTheme },
                        )
                        onDispose {}
                    }

                    ComposeLifeTheme(darkTheme) {
                        with(composeLifeAppUiCtx) {
                            ComposeLifeApp(
                                windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
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

/**
* The default light scrim, as defined by androidx and the platform:
* https://cs.android.com/androidx/platform/frameworks/support/+/androidx-main:activity/activity/src/main/java/androidx/activity/EdgeToEdge.kt;l=35-38;drc=27e7d52e8604a080133e8b842db10c89b4482598
*/
private val lightScrim = Color.argb(0xe6, 0xFF, 0xFF, 0xFF)

/**
 * The default dark scrim, as defined by androidx and the platform:
 * https://cs.android.com/androidx/platform/frameworks/support/+/androidx-main:activity/activity/src/main/java/androidx/activity/EdgeToEdge.kt;l=40-44;drc=27e7d52e8604a080133e8b842db10c89b4482598
 */
private val darkScrim = Color.argb(0x80, 0x1b, 0x1b, 0x1b)

@Suppress("LongMethod")
@OptIn(ExperimentalAnimatableApi::class)
fun ComponentActivity.setFancyContent(
    parent: CompositionContext? = null,
    content: @Composable () -> Unit,
) = setContent(parent) {
    val context = LocalContext.current
    val displayManager = requireNotNull(context.getSystemService<DisplayManager>())

    var displayChanged by remember { mutableIntStateOf(0) }

    DisposableEffect(context, displayManager) {
        val displayListener = object : DisplayManager.DisplayListener {
            override fun onDisplayAdded(displayId: Int) = Unit
            override fun onDisplayChanged(displayId: Int) {
                displayChanged++
            }
            override fun onDisplayRemoved(displayId: Int) = Unit
        }
        if (Build.VERSION.SDK_INT >= 36) {
            displayManager.registerDisplayListener(
                context.mainExecutor,
                DisplayManager.EVENT_TYPE_DISPLAY_CHANGED,
                displayListener,
            )
        } else {
            displayManager.registerDisplayListener(
                displayListener,
                Handler(context.mainLooper),
            )
        }
        onDispose {
            displayManager.unregisterDisplayListener(displayListener)
        }
    }

    /**
     * The rotation of the display relative to the natural orientation of the display.
     * This will be an integer number from 0 to 3.
     */
    val displayRotation = remember(
        context,
        LocalWindowInfo.current.containerSize,
        displayChanged,
    ) {
        ContextCompat.getDisplayOrDefault(context).rotation
    }
    val anim = remember { Animatable(displayRotation * 90f) }
    val targetRotation = remember(displayRotation) {
        val currentTargetValue = anim.targetValue
        val completeRotations = floor(currentTargetValue / 360f)
        listOf(
            (completeRotations - 1) * 360f + displayRotation * 90f,
            completeRotations * 360f + displayRotation * 90f,
            (completeRotations + 1) * 360f + displayRotation * 90f,
        ).minBy {
            abs(currentTargetValue - it)
        }
    }
    val currentTargetRotation by rememberUpdatedState(targetRotation)

    LaunchedEffect(Unit) {
        snapshotFlow { currentTargetRotation }
            .collect { newRotation ->
                launch {
                    anim.animateTo(
                        targetValue = newRotation,
                        animationSpec = spring(stiffness = Spring.StiffnessMediumLow),
                    )
                }
            }
    }
    LookaheadScope {
        Box(
            contentAlignment = Alignment.Center,
            modifier = Modifier
                .graphicsLayer {
                    rotationZ = (anim.value - targetRotation).mod(360f)
                }
                .animateContentSize(
                    animationSpec = spring(stiffness = Spring.StiffnessMedium),
                    alignment = Alignment.Center,
                    clip = false,
                ),
        ) {
            content()
        }
    }
}

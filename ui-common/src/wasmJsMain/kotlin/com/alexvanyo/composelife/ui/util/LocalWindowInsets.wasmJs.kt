/*
 * Copyright 2026 The Android Open Source Project
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
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.State
import androidx.compose.runtime.compositionLocalWithComputedDefaultOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.InternalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalPlatformWindowInsets
import androidx.compose.ui.platform.PlatformInsets
import androidx.compose.ui.platform.PlatformWindowInsets
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.dp
import kotlinx.browser.document
import kotlinx.browser.window
import org.w3c.dom.HTMLElement
import org.w3c.dom.events.Event

/**
 * Provides [LocalWindowInsetsHolder] and [LocalPlatformWindowInsets] with the updated value given by the safe-area
 * insets dispatched by the browser.
 */
@OptIn(InternalComposeUiApi::class)
@Composable
actual fun ProvideLocalWindowInsetsHolder(modifier: Modifier, content: @Composable () -> Unit) {
    val safeAreaInsets by rememberSafeAreaInsets()
    val density = LocalDensity.current
    val platformWindowInsets = remember(safeAreaInsets, density) {
        calculatePlatformWindowInsets(
            safeAreaInsets = safeAreaInsets,
            density = density,
        )
    }

    val windowInsetsHolder = remember {
        object : WindowInsetsHolder {}
    }

    CompositionLocalProvider(
        LocalWindowInsetsHolder provides windowInsetsHolder,
        LocalPlatformWindowInsets provides platformWindowInsets,
    ) {
        Box(
            propagateMinConstraints = true,
            modifier = modifier,
        ) {
            content()
        }
    }
}

@Composable
private fun rememberSafeAreaInsets(): State<WebSafeAreaInsets> {
    val safeAreaInsets = remember { mutableStateOf(WebSafeAreaInsets()) }

    DisposableEffect(Unit) {
        val insetsElement = createSafeAreaInsetsElement()
        document.body?.appendChild(insetsElement)

        val updateInsets = {
            val style = window.getComputedStyle(insetsElement)
            val newInsets = WebSafeAreaInsets(
                top = parsePx(style.getPropertyValue("padding-top")),
                bottom = parsePx(style.getPropertyValue("padding-bottom")),
                left = parsePx(style.getPropertyValue("padding-left")),
                right = parsePx(style.getPropertyValue("padding-right")),
            )
            if (newInsets != safeAreaInsets.value) {
                safeAreaInsets.value = newInsets
            }
        }

        updateInsets()

        val listener: (Event) -> Unit = { updateInsets() }

        window.addEventListener("resize", listener)
        window.addEventListener("orientationchange", listener)
        window.addEventListener("scroll", listener)
        document.addEventListener("fullscreenchange", listener)

        onDispose {
            window.removeEventListener("resize", listener)
            window.removeEventListener("orientationchange", listener)
            window.removeEventListener("scroll", listener)
            document.removeEventListener("fullscreenchange", listener)
            insetsElement.parentNode?.removeChild(insetsElement)
        }
    }

    return safeAreaInsets
}

private fun createSafeAreaInsetsElement(): HTMLElement = (document.createElement("div") as HTMLElement).apply {
    style.position = "fixed"
    style.top = "0"
    style.left = "0"
    style.width = "0"
    style.height = "0"
    style.visibility = "hidden"
    style.setProperty("pointer-events", "none")
    style.setProperty("padding-top", "env(safe-area-inset-top, 0px)")
    style.setProperty("padding-bottom", "env(safe-area-inset-bottom, 0px)")
    style.setProperty("padding-left", "env(safe-area-inset-left, 0px)")
    style.setProperty("padding-right", "env(safe-area-inset-right, 0px)")
}

@OptIn(InternalComposeUiApi::class)
private fun calculatePlatformWindowInsets(safeAreaInsets: WebSafeAreaInsets, density: Density): PlatformWindowInsets {
    val statusBars = with(density) {
        PlatformInsets(top = safeAreaInsets.top.dp)
    }
    val navigationBars = with(density) {
        PlatformInsets(
            left = safeAreaInsets.left.dp,
            right = safeAreaInsets.right.dp,
            bottom = safeAreaInsets.bottom.dp,
        )
    }
    val systemBars = with(density) {
        PlatformInsets(
            left = safeAreaInsets.left.dp,
            top = safeAreaInsets.top.dp,
            right = safeAreaInsets.right.dp,
            bottom = safeAreaInsets.bottom.dp,
        )
    }
    return WebPlatformWindowInsets(
        statusBars = statusBars,
        navigationBars = navigationBars,
        systemBars = systemBars,
    )
}

@InternalComposeUiApi
private class WebPlatformWindowInsets(
    override val statusBars: PlatformInsets,
    override val navigationBars: PlatformInsets,
    override val systemBars: PlatformInsets,
) : PlatformWindowInsets {
    override val displayCutout: PlatformInsets = systemBars
    override val tappableElement: PlatformInsets = navigationBars
    override val mandatorySystemGestures: PlatformInsets = navigationBars
    override val systemGestures: PlatformInsets = navigationBars

    override fun excluding(safeInsets: Boolean, ime: Boolean): PlatformWindowInsets =
        if (safeInsets) WebEmptyPlatformWindowInsets else this
}

@InternalComposeUiApi
private object WebEmptyPlatformWindowInsets : PlatformWindowInsets

internal data class WebSafeAreaInsets(
    val top: Float = 0f,
    val bottom: Float = 0f,
    val left: Float = 0f,
    val right: Float = 0f,
)

internal fun parsePx(value: String): Float = value.trim().removeSuffix("px").trim().toFloatOrNull() ?: 0f

actual interface WindowInsetsHolder

actual val LocalWindowInsetsHolder: ProvidableCompositionLocal<WindowInsetsHolder> =
    compositionLocalWithComputedDefaultOf {
        object : WindowInsetsHolder {}
    }

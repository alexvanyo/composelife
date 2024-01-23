/*
 * Copyright 2024 The Android Open Source Project
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

import android.content.Context
import android.content.res.Configuration
import android.graphics.Outline
import android.os.Build
import android.util.TypedValue
import android.view.ContextThemeWrapper
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.ViewOutlineProvider
import android.view.Window
import android.view.WindowManager
import androidx.activity.ComponentActivity
import androidx.activity.ComponentDialog
import androidx.activity.enableEdgeToEdge
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.animateFloatAsState
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.safeDrawingPadding
import androidx.compose.foundation.layout.widthIn
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionContext
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.SideEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCompositionContext
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.TransformOrigin
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.platform.AbstractComposeView
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.platform.LocalView
import androidx.compose.ui.platform.ViewRootForInspector
import androidx.compose.ui.semantics.dialog
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.lerp
import androidx.compose.ui.util.fastForEach
import androidx.compose.ui.util.fastMap
import androidx.compose.ui.util.fastMaxBy
import androidx.compose.ui.util.lerp
import androidx.compose.ui.window.Dialog
import androidx.compose.ui.window.DialogProperties
import androidx.compose.ui.window.DialogWindowProvider
import androidx.compose.ui.window.SecureFlagPolicy
import androidx.core.view.WindowCompat
import androidx.lifecycle.findViewTreeLifecycleOwner
import androidx.lifecycle.findViewTreeViewModelStoreOwner
import androidx.lifecycle.setViewTreeLifecycleOwner
import androidx.lifecycle.setViewTreeViewModelStoreOwner
import androidx.savedstate.findViewTreeSavedStateRegistryOwner
import androidx.savedstate.setViewTreeSavedStateRegistryOwner
import com.alexvanyo.composelife.ui.common.R
import java.util.UUID

/**
 * A [Dialog] that is _always_ edge-to-edge. This is intended to be the underlying backbone for more complicated and
 * opinionated dialogs.
 *
 * The [content] will fill the entire window, going entirely edge-to-edge.
 *
 * This [EdgeToEdgeDialog] provides no scrim or dismissing when the scrim is pressed: if this is desired, it must be
 * implemented by the [content]. For the most simple implementation of this that acts like a platform dialog, use
 * [PlatformEdgeToEdgeDialog].
 *
 * [DialogProperties] will be respected, but [DialogProperties.decorFitsSystemWindows] and
 * [DialogProperties.usePlatformDefaultWidth] are ignored.
 *
 * The [content] will be passed a [CompletablePredictiveBackStateHolder] that encapsulates the predictive back state if
 * [DialogProperties.dismissOnBackPress] is true.
 */
@Composable
fun EdgeToEdgeDialog(
    onDismissRequest: () -> Unit,
    properties: DialogProperties = DialogProperties(),
    content: @Composable (CompletablePredictiveBackStateHolder) -> Unit,
) {
    val view = LocalView.current
    val density = LocalDensity.current
    val layoutDirection = LocalLayoutDirection.current
    val composition = rememberCompositionContext()
    val dialogId = rememberSaveable { UUID.randomUUID() }
    val currentOnDismissRequest by rememberUpdatedState(onDismissRequest)
    val currentDismissOnBackPress by rememberUpdatedState(properties.dismissOnBackPress)
    val currentContent by rememberUpdatedState(content)

    val dialog = remember(view, density) {
        DialogWrapper(
            onDismissRequest = onDismissRequest,
            properties = properties,
            composeView = view,
            layoutDirection = layoutDirection,
            density = density,
            dialogId = dialogId,
        ).apply {
            setContent(composition) {
                val completablePredictiveBackStateHolder = rememberCompletablePredictiveBackStateHolder()

                CompletablePredictiveBackStateHandler(
                    completablePredictiveBackStateHolder = completablePredictiveBackStateHolder,
                    enabled = currentDismissOnBackPress,
                    onBack = { currentOnDismissRequest() },
                )

                DialogLayout(
                    Modifier.semantics { dialog() },
                ) {
                    currentContent(completablePredictiveBackStateHolder)
                }
            }
        }
    }

    DisposableEffect(dialog) {
        dialog.show()

        onDispose {
            dialog.dismiss()
            dialog.disposeComposition()
        }
    }

    SideEffect {
        dialog.updateParameters(
            onDismissRequest = onDismissRequest,
            properties = properties,
            layoutDirection = layoutDirection,
        )
    }
}

/**
 * A [Dialog] based on [EdgeToEdgeDialog] that provides a more opinionated dialog that is closer to the default
 * [Dialog].
 *
 * The [scrim] is rendered behind the content. The default scrim will request to dismiss the dialog if
 * [DialogProperties.dismissOnClickOutside] is true.
 *
 * The [content] of the dialog can be arbitrarily sized, and can fill the entire window if desired.
 *
 * If [DialogProperties.dismissOnBackPress] is true, the [content] will automatically start to animate out with a
 * predictive back gestures from the dialog.
 */
@Suppress("ComposeModifierMissing", "LongMethod", "CyclomaticComplexMethod")
@Composable
fun PlatformEdgeToEdgeDialog(
    onDismissRequest: () -> Unit,
    properties: DialogProperties = DialogProperties(),
    scrim: @Composable () -> Unit = {
        val scrimColor = Color.Black.copy(alpha = 0.6f)
        Canvas(
            modifier = Modifier
                .fillMaxSize()
                .then(
                    if (properties.dismissOnClickOutside) {
                        Modifier.pointerInput(Unit) {
                            detectTapGestures { onDismissRequest() }
                        }
                    } else {
                        Modifier
                    },
                ),
        ) {
            drawRect(
                color = scrimColor,
                topLeft = -Offset(size.width, size.height),
                size = size * 3f,
            )
        }
    },
    content: @Composable () -> Unit,
) = EdgeToEdgeDialog(
    onDismissRequest = onDismissRequest,
    properties = properties,
) { predictiveBackStateHolder ->
    Box(
        modifier = Modifier.fillMaxSize(),
        contentAlignment = Alignment.Center,
    ) {
        scrim()

        val sizeModifier = if (properties.usePlatformDefaultWidth) {
            // This is a reimplementation of the intrinsic logic from
            // https://cs.android.com/android/platform/superproject/main/+/main:frameworks/base/core/java/com/android/internal/policy/DecorView.java;l=757;drc=e41472bd05b233b5946b30b3d862f043c30f54c7
            val context = LocalContext.current
            val widthResource = if (LocalConfiguration.current.orientation == Configuration.ORIENTATION_PORTRAIT) {
                android.R.dimen.dialog_min_width_minor
            } else {
                android.R.dimen.dialog_min_width_major
            }
            val typedValue = TypedValue().also {
                context.resources.getValue(widthResource, it, true)
            }
            when (typedValue.type) {
                TypedValue.TYPE_DIMENSION -> {
                    Modifier.widthIn(
                        min = with(LocalDensity.current) {
                            typedValue.getDimension(context.resources.displayMetrics).toDp()
                        },
                    )
                }
                TypedValue.TYPE_FRACTION ->
                    Modifier.fillMaxWidth(fraction = typedValue.getFraction(1f, 1f))
                else -> Modifier
            }
        } else {
            Modifier
        }

        val predictiveBackState = predictiveBackStateHolder.value

        val lastRunningValue by remember {
            mutableStateOf<CompletablePredictiveBackState.Running?>(null)
        }.apply {
            when (predictiveBackState) {
                CompletablePredictiveBackState.NotRunning -> value = null
                is CompletablePredictiveBackState.Running -> if (predictiveBackState.progress >= 0.01f) {
                    // Only save that we were disappearing if the progress is at least 1% along
                    value = predictiveBackState
                }
                CompletablePredictiveBackState.Completed -> Unit
            }
        }
        val scale by animateFloatAsState(
            targetValue = when (predictiveBackState) {
                CompletablePredictiveBackState.NotRunning -> 1f
                is CompletablePredictiveBackState.Running -> lerp(1f, 0.9f, predictiveBackState.progress)
                CompletablePredictiveBackState.Completed -> 0.9f
            },
            label = "scale",
        ) {
        }
        val translationX by animateDpAsState(
            targetValue = when (predictiveBackState) {
                CompletablePredictiveBackState.NotRunning -> 0.dp
                is CompletablePredictiveBackState.Running -> lerp(
                    0.dp,
                    8.dp,
                    predictiveBackState.progress,
                ) * when (predictiveBackState.swipeEdge) {
                    SwipeEdge.Left -> -1f
                    SwipeEdge.Right -> 1f
                }
                CompletablePredictiveBackState.Completed -> {
                    8.dp * when (lastRunningValue?.swipeEdge) {
                        null -> 0f
                        SwipeEdge.Left -> -1f
                        SwipeEdge.Right -> 1f
                    }
                }
            },
            label = "translationX",
        )
        val pivotFractionX by animateFloatAsState(
            targetValue = when (predictiveBackState) {
                CompletablePredictiveBackState.NotRunning -> 0.5f
                is CompletablePredictiveBackState.Running -> when (predictiveBackState.swipeEdge) {
                    SwipeEdge.Left -> 1f
                    SwipeEdge.Right -> 0f
                }
                CompletablePredictiveBackState.Completed -> {
                    when (lastRunningValue?.swipeEdge) {
                        null -> 0.5f
                        SwipeEdge.Left -> 1f
                        SwipeEdge.Right -> 0f
                    }
                }
            },
            label = "pivotFractionX",
        )

        Box(
            modifier = Modifier
                .safeDrawingPadding()
                .graphicsLayer {
                    this.translationX = translationX.toPx()
                    this.alpha = alpha
                    this.scaleX = scale
                    this.scaleY = scale
                    this.transformOrigin = TransformOrigin(pivotFractionX, 0.5f)
                }
                .then(sizeModifier),
            contentAlignment = Alignment.Center,
        ) {
            content()
        }
    }
}

private class DialogWrapper(
    private var onDismissRequest: () -> Unit,
    private var properties: DialogProperties,
    private val composeView: View,
    layoutDirection: LayoutDirection,
    density: Density,
    dialogId: UUID,
) : ComponentDialog(
    /**
     * [Window.setClipToOutline] is only available from 22+, but the style attribute exists on 21.
     * So use a wrapped context that sets this attribute for compatibility back to 21.
     */
    ContextThemeWrapper(
        composeView.context,
        R.style.EdgeToEdgeFloatingDialogWindowTheme,
    ),
),
    ViewRootForInspector {

    private val dialogLayout: DialogLayout

    // On systems older than Android S, there is a bug in the surface insets matrix math used by
    // elevation, so high values of maxSupportedElevation break accessibility services: b/232788477.
    private val maxSupportedElevation = 8.dp

    override val subCompositionView: AbstractComposeView get() = dialogLayout

    init {
        val window = window ?: error("Dialog has no window")
        WindowCompat.setDecorFitsSystemWindows(window, false)
        dialogLayout = DialogLayout(context, window).apply {
            // Set unique id for AbstractComposeView. This allows state restoration for the state
            // defined inside the Dialog via rememberSaveable()
            setTag(R.id.compose_view_saveable_id_tag, "Dialog:$dialogId")
            // Enable children to draw their shadow by not clipping them
            clipChildren = false
            // Allocate space for elevation
            with(density) { elevation = maxSupportedElevation.toPx() }
            // Simple outline to force window manager to allocate space for shadow.
            // Note that the outline affects clickable area for the dismiss listener. In case of
            // shapes like circle the area for dismiss might be to small (rectangular outline
            // consuming clicks outside of the circle).
            outlineProvider = object : ViewOutlineProvider() {
                override fun getOutline(view: View, result: Outline) {
                    result.setRect(0, 0, view.width, view.height)
                    // We set alpha to 0 to hide the view's shadow and let the composable to draw
                    // its own shadow. This still enables us to get the extra space needed in the
                    // surface.
                    result.alpha = 0f
                }
            }
        }

        /**
         * Disables clipping for [this] and all its descendant [ViewGroup]s until we reach a
         * [DialogLayout] (the [ViewGroup] containing the Compose hierarchy).
         */
        fun ViewGroup.disableClipping() {
            clipChildren = false
            if (this is DialogLayout) return
            for (i in 0 until childCount) {
                (getChildAt(i) as? ViewGroup)?.disableClipping()
            }
        }

        // Turn of all clipping so shadows can be drawn outside the window
        (window.decorView as? ViewGroup)?.disableClipping()
        setContentView(dialogLayout)
        dialogLayout.setViewTreeLifecycleOwner(composeView.findViewTreeLifecycleOwner())
        dialogLayout.setViewTreeViewModelStoreOwner(composeView.findViewTreeViewModelStoreOwner())
        dialogLayout.setViewTreeSavedStateRegistryOwner(
            composeView.findViewTreeSavedStateRegistryOwner(),
        )

        // Initial setup
        updateParameters(onDismissRequest, properties, layoutDirection)
    }

    private fun setLayoutDirection(layoutDirection: LayoutDirection) {
        dialogLayout.layoutDirection = when (layoutDirection) {
            LayoutDirection.Ltr -> android.util.LayoutDirection.LTR
            LayoutDirection.Rtl -> android.util.LayoutDirection.RTL
        }
    }

    fun setContent(
        parentComposition: CompositionContext,
        children: @Composable () -> Unit,
    ) {
        dialogLayout.setContent(parentComposition, children)
    }

    private fun setSecurePolicy(securePolicy: SecureFlagPolicy) {
        val secureFlagEnabled =
            when (securePolicy) {
                SecureFlagPolicy.SecureOff -> false
                SecureFlagPolicy.SecureOn -> true
                SecureFlagPolicy.Inherit -> composeView.isFlagSecureEnabled()
            }
        checkNotNull(window).setFlags(
            if (secureFlagEnabled) {
                WindowManager.LayoutParams.FLAG_SECURE
            } else {
                WindowManager.LayoutParams.FLAG_SECURE.inv()
            },
            WindowManager.LayoutParams.FLAG_SECURE,
        )
    }

    fun updateParameters(
        onDismissRequest: () -> Unit,
        properties: DialogProperties,
        layoutDirection: LayoutDirection,
    ) {
        this.onDismissRequest = onDismissRequest
        this.properties = properties
        setSecurePolicy(properties.securePolicy)
        setLayoutDirection(layoutDirection)
        window?.setLayout(
            WindowManager.LayoutParams.MATCH_PARENT,
            WindowManager.LayoutParams.MATCH_PARENT,
        )
        window?.setSoftInputMode(
            if (Build.VERSION.SDK_INT >= 30) {
                WindowManager.LayoutParams.SOFT_INPUT_ADJUST_NOTHING
            } else {
                @Suppress("DEPRECATION")
                WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE
            },
        )
    }

    fun disposeComposition() {
        dialogLayout.disposeComposition()
    }

    override fun onTouchEvent(event: MotionEvent): Boolean {
        val result = super.onTouchEvent(event)
        if (result && properties.dismissOnClickOutside) {
            onDismissRequest()
        }

        return result
    }

    override fun cancel() {
        // Prevents the dialog from dismissing itself
        return
    }
}

@Suppress("ViewConstructor")
private class DialogLayout(
    context: Context,
    override val window: Window,
) : AbstractComposeView(context), DialogWindowProvider {

    private var content: @Composable () -> Unit by mutableStateOf({})

    override var shouldCreateCompositionOnAttachedToWindow: Boolean = false
        private set

    fun setContent(parent: CompositionContext, content: @Composable () -> Unit) {
        setParentCompositionContext(parent)
        this.content = content
        shouldCreateCompositionOnAttachedToWindow = true
        createComposition()
    }

    @Composable
    override fun Content() {
        content()
    }
}

@Composable
private fun DialogLayout(
    modifier: Modifier = Modifier,
    content: @Composable () -> Unit,
) {
    Layout(
        content = content,
        modifier = modifier,
    ) { measurables, constraints ->
        val placeables = measurables.fastMap { it.measure(constraints) }
        val width = placeables.fastMaxBy { it.width }?.width ?: constraints.minWidth
        val height = placeables.fastMaxBy { it.height }?.height ?: constraints.minHeight
        layout(width, height) {
            placeables.fastForEach { it.placeRelative(0, 0) }
        }
    }
}

internal fun View.isFlagSecureEnabled(): Boolean {
    val windowParams = rootView.layoutParams as? WindowManager.LayoutParams
    if (windowParams != null) {
        return (windowParams.flags and WindowManager.LayoutParams.FLAG_SECURE) != 0
    }
    return false
}

@Suppress("LongMethod")
@Preview
@Composable
fun EdgeToEdgeDialogPreview() {
    var showEdgeToEdgeDialog by remember { mutableStateOf(false) }
    var showBuiltInDialog by remember { mutableStateOf(false) }
    var showPlatformEdgeToEdgeDialog by remember { mutableStateOf(false) }

    val context = LocalContext.current
    SideEffect {
        (context as? ComponentActivity)?.enableEdgeToEdge()
    }

    Column(
        modifier = Modifier.fillMaxSize(),
        horizontalAlignment = Alignment.CenterHorizontally,
        verticalArrangement = Arrangement.Center,
    ) {
        BasicText(
            modifier = Modifier
                .height(64.dp)
                .clickable { showEdgeToEdgeDialog = true },
            text = "Show edge-to-edge dialog",
        )
        BasicText(
            modifier = Modifier
                .height(64.dp)
                .clickable { showBuiltInDialog = true },
            text = "Show built-in dialog",
        )
        BasicText(
            modifier = Modifier
                .height(64.dp)
                .clickable { showPlatformEdgeToEdgeDialog = true },
            text = "Show platform edge-to-edge dialog",
        )
    }

    val hideEdgeToEdgeDialog = { showEdgeToEdgeDialog = false }

    if (showEdgeToEdgeDialog) {
        EdgeToEdgeDialog(
            onDismissRequest = hideEdgeToEdgeDialog,
        ) {
            Box(
                modifier = Modifier.fillMaxSize(),
                contentAlignment = Alignment.Center,
            ) {
                val scrimColor = Color.Black.copy(alpha = 0.6f)
                Canvas(
                    modifier = Modifier
                        .fillMaxSize()
                        .pointerInput(Unit) {
                            detectTapGestures { hideEdgeToEdgeDialog() }
                        },
                ) {
                    drawRect(
                        color = scrimColor,
                        topLeft = -Offset(size.width, size.height),
                        size = size * 3f,
                    )
                }
                Box(
                    modifier = Modifier
                        .fillMaxSize()
                        .background(Color.Red)
                        .pointerInput(Unit) {},
                    contentAlignment = Alignment.Center,
                ) {
                    BasicText("Full screen")
                }
            }
        }
    }

    if (showBuiltInDialog) {
        Dialog(
            onDismissRequest = { showBuiltInDialog = false },
        ) {
            Box(
                modifier = Modifier
                    .fillMaxSize()
                    .background(Color.Red),
                contentAlignment = Alignment.Center,
            ) {
                BasicText("Full screen")
            }
        }
    }

    if (showPlatformEdgeToEdgeDialog) {
        PlatformEdgeToEdgeDialog(
            onDismissRequest = { showPlatformEdgeToEdgeDialog = false },
        ) {
            Box(
                modifier = Modifier
                    .fillMaxSize()
                    .background(Color.Red)
                    .pointerInput(Unit) {},
                contentAlignment = Alignment.Center,
            ) {
                BasicText("Full screen")
            }
        }
    }
}

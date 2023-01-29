/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.wear

import android.os.Bundle
import androidx.activity.compose.setContent
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.foundation.Image
import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.focusable
import androidx.compose.foundation.gestures.awaitEachGesture
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.alpha
import androidx.compose.ui.draw.clip
import androidx.compose.ui.draw.drawWithContent
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Brush
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.graphics.compositeOver
import androidx.compose.ui.graphics.toArgb
import androidx.compose.ui.input.pointer.pointerInput
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.res.imageResource
import androidx.compose.ui.res.stringResource
import androidx.lifecycle.lifecycleScope
import androidx.wear.compose.foundation.HierarchicalFocusCoordinator
import androidx.wear.compose.foundation.lazy.AutoCenteringParams
import androidx.wear.compose.foundation.lazy.ScalingLazyColumn
import androidx.wear.compose.foundation.lazy.ScalingLazyListState
import androidx.wear.compose.foundation.lazy.rememberScalingLazyListState
import androidx.wear.compose.foundation.rememberActiveFocusRequester
import androidx.wear.compose.material.Chip
import androidx.wear.compose.material.ChipDefaults
import androidx.wear.compose.material.CircularProgressIndicator
import androidx.wear.compose.material.MaterialTheme
import androidx.wear.compose.material.Picker
import androidx.wear.compose.material.PickerDefaults
import androidx.wear.compose.material.PositionIndicator
import androidx.wear.compose.material.Scaffold
import androidx.wear.compose.material.SwipeToDismissBox
import androidx.wear.compose.material.Text
import androidx.wear.compose.material.rememberPickerState
import androidx.wear.watchface.DrawMode
import androidx.wear.watchface.RenderParameters
import androidx.wear.watchface.editor.EditorSession
import androidx.wear.watchface.style.WatchFaceLayer
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.MutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import com.alexvanyo.composelife.ui.util.ColorComponent
import com.alexvanyo.composelife.ui.util.WearDevicePreviews
import com.alexvanyo.composelife.ui.util.get
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.alexvanyo.composelife.ui.util.values
import com.alexvanyo.composelife.ui.util.withComponent
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.wear.theme.ComposeLifeTheme
import com.google.android.horologist.compose.rotaryinput.onRotaryInputAccumulated
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield
import java.util.UUID

class WatchFaceConfigActivity : AppCompatActivity() {

    private lateinit var editorSession: EditorSession

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        lifecycleScope.launch {
            editorSession = EditorSession.createOnWatchEditorSession(this@WatchFaceConfigActivity)
        }

        setContent {
            val watchFaceConfigState = rememberWatchFaceConfigState(editorSession)
            LaunchedEffect(watchFaceConfigState) {
                watchFaceConfigState.update()
            }
            ComposeLifeTheme {
                WatchFaceConfigScreen(
                    state = watchFaceConfigState,
                    modifier = Modifier.background(MaterialTheme.colors.background),
                )
            }
        }
    }
}

interface WatchFaceConfigState : Updatable {
    val preview: ImageBitmap?

    var color: Color

    fun openComplicationDataSourceChooser(id: Int)
}

@Composable
fun rememberWatchFaceConfigState(
    editorSession: EditorSession
): WatchFaceConfigState {
    val coroutineScope = rememberCoroutineScope()

    var preview: ImageBitmap? by remember { mutableStateOf(null) }

    return remember(editorSession) {
        object : WatchFaceConfigState {
            override val preview: ImageBitmap? get() = preview

            override var color: Color by mutableStateOf(
                with(editorSession.userStyleSchema) {
                    editorSession.userStyle.value.getGameOfLifeColor()
                }
            )

            override fun openComplicationDataSourceChooser(id: Int) {
                coroutineScope.launch {
                    editorSession.openComplicationDataSourceChooser(id)
                }
            }

            override suspend fun update(): Nothing = coroutineScope {
                launch {
                    combine(
                        editorSession.userStyle,
                        editorSession.complicationsPreviewData,
                    ) { _, complicationsPreviewData ->
                        yield()
                        preview = editorSession.renderWatchFaceToBitmap(
                            renderParameters = RenderParameters(
                                DrawMode.INTERACTIVE,
                                WatchFaceLayer.ALL_WATCH_FACE_LAYERS,
                                RenderParameters.HighlightLayer(
                                    RenderParameters.HighlightedElement.AllComplicationSlots,
                                    Color.Red.toArgb(),
                                    Color(0, 0, 0, 128).toArgb(),
                                )
                            ),
                            instant = editorSession.previewReferenceInstant,
                            slotIdToComplicationData = complicationsPreviewData,
                        ).asImageBitmap()
                    }
                        .collect {}
                }

                launch {
                    snapshotFlow { color }
                        .collect { newColor ->
                            editorSession.userStyle.value =
                                editorSession.userStyle.value.toMutableUserStyle().apply {
                                    with(editorSession.userStyleSchema) {
                                        setGameOfLifeColor(newColor)
                                    }
                                }.toUserStyle()
                        }
                }
            }.let { error("combine should not complete normally") }
        }
    }
}

sealed interface WatchFaceConfigNavigation {
    object List : WatchFaceConfigNavigation
    object ColorPicker : WatchFaceConfigNavigation

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}

@Composable
fun WatchFaceConfigScreen(
    state: WatchFaceConfigState,
    modifier: Modifier = Modifier,
) {
    val navigationController =
        rememberMutableBackstackNavigationController(
            initialBackstackEntries = listOf(
                BackstackEntry(
                    value = WatchFaceConfigNavigation.List,
                    previous = null,
                ),
            ),
            saver = WatchFaceConfigNavigation.Saver
        )

    val listScalingLazyColumnState = rememberScalingLazyListState(
        initialCenterItemIndex = 0,
    )

    Scaffold(
        positionIndicator = when (navigationController.currentEntry.value) {
            WatchFaceConfigNavigation.List -> {
                {
                    PositionIndicator(listScalingLazyColumnState)
                }
            }
            WatchFaceConfigNavigation.ColorPicker -> null
        },
        modifier = modifier,
    ) {
        WearNavigationHost(
            navigationController = navigationController
        ) { entry ->
            when (entry.value) {
                WatchFaceConfigNavigation.List -> {
                    WatchFaceConfigList(
                        state = state,
                        onEditColorClicked = {
                            navigationController.withExpectedActor(entry.id) {
                                navigate(WatchFaceConfigNavigation.ColorPicker)
                            }
                        },
                        scalingLazyListState = listScalingLazyColumnState
                    )
                }
                WatchFaceConfigNavigation.ColorPicker -> {
                    WatchFaceColorPicker(
                        color = state.color,
                        setColor = { state.color = it }
                    )
                }
            }
        }
    }
}

@Composable
fun WatchFaceColorPicker(
    color: Color,
    setColor: (Color) -> Unit,
    modifier: Modifier = Modifier,
) {
    var selectedComponent: ColorComponent.RgbIntComponent by rememberSaveable(
        stateSaver = ColorComponent.RgbIntComponent.Saver
    ) {
        mutableStateOf(ColorComponent.RgbIntComponent.Red)
    }

    val gradientColor = MaterialTheme.colors.background
    val gradientRatio = PickerDefaults.DefaultGradientRatio

    Row(
        modifier
            .fillMaxSize()
            .drawWithContent {
                drawRect(color.copy(alpha = 0.5f))
                drawContent()
                drawRect(
                    Brush.linearGradient(
                        colors = listOf(gradientColor, Color.Transparent),
                        start = Offset(size.width / 2, 0f),
                        end = Offset(size.width / 2, size.height * gradientRatio)
                    )
                )
                drawRect(
                    Brush.linearGradient(
                        colors = listOf(Color.Transparent, gradientColor),
                        start = Offset(size.width / 2, size.height * (1 - gradientRatio)),
                        end = Offset(size.width / 2, size.height)
                    )
                )
            }
    ) {
        Spacer(Modifier.weight(1f))
        ColorComponent.RgbIntComponent.values.forEach { component ->
            key(component) {
                ColorComponentPicker(
                    isSelected = selectedComponent == component,
                    onSelected = { selectedComponent = component },
                    initialComponentValue = color.get(component),
                    setComponentValue = {
                        setColor(color.withComponent(component, it))
                    },
                    contentDescription = stringResource(
                        when (component) {
                            ColorComponent.RgbIntComponent.Red -> R.string.color_red_value
                            ColorComponent.RgbIntComponent.Green -> R.string.color_green_value
                            ColorComponent.RgbIntComponent.Blue -> R.string.color_blue_value
                        }
                    ),
                    modifier = Modifier.weight(2f),
                )
            }
        }
        Spacer(Modifier.weight(1f))
    }
}

@Composable
@Suppress("LongParameterList")
fun ColorComponentPicker(
    isSelected: Boolean,
    onSelected: () -> Unit,
    initialComponentValue: Int,
    setComponentValue: (Int) -> Unit,
    contentDescription: String,
    modifier: Modifier = Modifier,
) {
    val pickerState = rememberPickerState(
        initialNumberOfOptions = 256,
        initiallySelectedOption = remember { initialComponentValue }
    )
    val currentSetComponentValue by rememberUpdatedState(setComponentValue)

    val coroutineScope = rememberCoroutineScope()

    LaunchedEffect(pickerState) {
        snapshotFlow { pickerState.selectedOption }
            .collect {
                currentSetComponentValue(it)
            }
    }

    HierarchicalFocusCoordinator(
        requiresFocus = { isSelected }
    ) {
        Picker(
            state = pickerState,
            contentDescription = contentDescription,
            onSelected = onSelected,
            gradientRatio = 0f,
            modifier = modifier
                .onRotaryInputAccumulated {
                    coroutineScope.launch {
                        pickerState.scrollToOption(pickerState.selectedOption + if (it > 0) 1 else -1)
                    }
                }
                .focusRequester(rememberActiveFocusRequester())
                .focusable(),
        ) { optionIndex ->
            Box(
                contentAlignment = Alignment.Center,
                modifier = Modifier
                    .fillMaxSize()
                    .pointerInput(Unit) {
                        awaitEachGesture {
                            awaitFirstDown()
                            onSelected()
                        }
                    },
            ) {
                Text(
                    text = "%02X".format(optionIndex),
                    style = MaterialTheme.typography.display2,
                    modifier = Modifier.alpha(if (isSelected) 1f else 0.5f)
                )
            }
        }
    }
}

@Composable
fun WatchFaceConfigList(
    state: WatchFaceConfigState,
    onEditColorClicked: () -> Unit,
    modifier: Modifier = Modifier,
    scalingLazyListState: ScalingLazyListState,
) {
    ScalingLazyColumn(
        modifier = modifier,
        state = scalingLazyListState,
        autoCentering = AutoCenteringParams(itemIndex = 0)
    ) {
        item {
            Box(
                contentAlignment = Alignment.Center,
                modifier = Modifier.fillMaxWidth(),
            ) {
                val currentPreview = state.preview
                if (currentPreview != null) {
                    WatchFacePreview(
                        previewImageBitmap = currentPreview,
                        onComplicationClicked = { id ->
                            state.openComplicationDataSourceChooser(id)
                        },
                        modifier = Modifier.fillMaxWidth(0.8f)
                    )
                } else {
                    Box(
                        contentAlignment = Alignment.Center,
                        modifier = Modifier
                            .fillMaxWidth(0.8f)
                            .aspectRatio(1f)
                            .fillMaxHeight()
                    ) {
                        CircularProgressIndicator()
                    }
                }
            }
        }
        item {
            Chip(
                label = {
                    Text(text = stringResource(id = R.string.color))
                },
                onClick = onEditColorClicked,
                colors = ChipDefaults.gradientBackgroundChipColors(
                    startBackgroundColor = MaterialTheme.colors.surface.copy(alpha = 0f)
                        .compositeOver(MaterialTheme.colors.surface),
                    endBackgroundColor = state.color.copy(alpha = 0.5f)
                        .compositeOver(MaterialTheme.colors.surface),
                ),
                modifier = Modifier.fillMaxWidth()
            )
        }
    }
}

@WearDevicePreviews
@Composable
fun WatchFaceConfigScreenPreview() {
    ComposeLifeTheme {
        val preview = ImageBitmap.imageResource(id = R.drawable.watchface_square)

        WatchFaceConfigScreen(
            state = object : WatchFaceConfigState {
                override suspend fun update(): Nothing = awaitCancellation()

                override var color: Color = Color.White

                override val preview get() = preview

                override fun openComplicationDataSourceChooser(id: Int) = Unit
            }
        )
    }
}

@Composable
fun WatchFacePreview(
    previewImageBitmap: ImageBitmap,
    onComplicationClicked: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    val aspectRatio = previewImageBitmap.width.toFloat() / previewImageBitmap.height
    Box(
        modifier = modifier.aspectRatio(aspectRatio)
    ) {
        Image(
            bitmap = previewImageBitmap,
            contentDescription = "Preview",
            modifier = Modifier
                .fillMaxWidth()
                .then(
                    if (LocalConfiguration.current.isScreenRound) {
                        Modifier.clip(CircleShape)
                    } else {
                        Modifier
                    }
                )
        )

        GameOfLifeComplication.values.forEach { gameOfLifeComplication ->
            Column(
                Modifier.fillMaxSize()
            ) {
                Spacer(
                    modifier = Modifier.weight(gameOfLifeComplication.rawBounds.top)
                )

                Row(
                    Modifier
                        .fillMaxWidth()
                        .weight(gameOfLifeComplication.rawBounds.height)
                ) {
                    Spacer(
                        modifier = Modifier.weight(gameOfLifeComplication.rawBounds.left)
                    )

                    Box(
                        Modifier
                            .fillMaxSize()
                            .weight(gameOfLifeComplication.rawBounds.width)
                            .clickable {
                                onComplicationClicked(gameOfLifeComplication.id)
                            }
                    )

                    Spacer(
                        modifier = Modifier.weight(1f - gameOfLifeComplication.rawBounds.right)
                    )
                }

                Spacer(
                    modifier = Modifier.weight(1f - gameOfLifeComplication.rawBounds.bottom)
                )
            }
        }
    }
}

@WearDevicePreviews
@Composable
fun WatchFacePreviewPreview() {
    WatchFacePreview(
        previewImageBitmap = ImageBitmap.imageResource(R.drawable.watchface_square),
        onComplicationClicked = {},
    )
}

@Composable
fun <T> WearNavigationHost(
    navigationController: MutableBackstackNavigationController<T>,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.map(UUID::toString) },
            restore = {
                mutableStateSetOf<UUID>().apply {
                    addAll(it.map(UUID::fromString))
                }
            },
        ),
    ) { mutableStateSetOf<UUID>() }

    SwipeToDismissBox(
        onDismissed = { navigationController.popBackstack() },
        backgroundKey = navigationController.currentEntry.previous?.id ?: remember { UUID.randomUUID() },
        contentKey = navigationController.currentEntry.id,
        hasBackground = navigationController.canNavigateBack,
        modifier = modifier,
    ) { isBackground ->
        val entry = if (isBackground) {
            checkNotNull(navigationController.currentEntry.previous) {
                "Current entry had no previous, should not be showing background!"
            }
        } else {
            navigationController.currentEntry
        }

        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet: Set<UUID> = navigationController.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
        (allKeys - keySet).forEach(stateHolder::removeState)
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.addAll(keySet)
    }
}

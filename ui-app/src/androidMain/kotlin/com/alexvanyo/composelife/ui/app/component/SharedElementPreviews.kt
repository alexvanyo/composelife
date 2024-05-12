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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionScope
import androidx.compose.foundation.background
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.FlowRow
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.requiredSizeIn
import androidx.compose.foundation.layout.size
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.Placeable
import androidx.compose.ui.text.input.TextFieldValue
import androidx.compose.ui.text.style.TextOverflow
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingUi
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews
import com.alexvanyo.composelife.ui.util.TargetState

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun AnimatedContentSharedElement() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            AnimatedContent(isExpanded, modifier = modifier) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElement(
                                rememberSharedContentState(key = "a"),
                                this,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElement(
                                    rememberSharedContentState(key = "a"),
                                    this@AnimatedContent,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun AnimatedContentSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            AnimatedContent(isExpanded, modifier = modifier) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElementWithCallerManagedVisibility(
                                rememberSharedContentState(key = "a"),
                                isExpanded,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun CustomAnimatedContentSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    Box(modifier = Modifier.size(256.dp)) {
        SharedTransitionScope { modifier ->
            com.alexvanyo.composelife.ui.util.AnimatedContent(
                TargetState.Single(isExpanded),
                modifier = modifier,
            ) { targetState ->
                if (targetState) {
                    Box(
                        modifier = Modifier
                            .sharedElementWithCallerManagedVisibility(
                                rememberSharedContentState(key = "a"),
                                isExpanded,
                            )
                            .fillMaxSize()
                            .background(Color.Red)
                            .clickable {
                                isExpanded = !isExpanded
                            },
                    )
                } else {
                    FlowRow {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                )
                                .size(64.dp)
                                .background(Color.Magenta)
                                .clickable {
                                    isExpanded = !isExpanded
                                },
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .size(64.dp)
                                .background(Color.Yellow),
                        )
                    }
                }
            }
        }
    }
}

@OptIn(ExperimentalSharedTransitionApi::class, ExperimentalLayoutApi::class)
@Preview
@Composable
internal fun CustomAnimatedContentSettingUiSharedElementWithCallerManagedVisibility() {
    var isExpanded by remember { mutableStateOf(false) }

    WithPreviewDependencies {
        Surface {
            SharedTransitionScope { modifier ->
                com.alexvanyo.composelife.ui.util.AnimatedContent(
                    TargetState.Single(isExpanded),
                    modifier = modifier
                        .fillMaxSize()
                        .clickable { isExpanded = !isExpanded },
                ) { targetState ->
                    if (targetState) {
                        Column(verticalArrangement = Arrangement.Top, modifier = Modifier.fillMaxSize()) {
                            SettingUi(
                                setting = Setting.CellShapeConfig,
                                onOpenInSettingsClicked = null,
                                modifier = Modifier.sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    isExpanded,
                                ),
                            )
                        }
                    } else {
                        Column(verticalArrangement = Arrangement.Bottom, modifier = Modifier.fillMaxSize()) {
                            SettingUi(
                                setting = Setting.CellShapeConfig,
                                onOpenInSettingsClicked = {},
                                modifier = Modifier.sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "a"),
                                    !isExpanded,
                                ),
                            )
                        }
                    }
                }
            }
        }
    }
}

@Suppress("LongMethod")
@OptIn(ExperimentalSharedTransitionApi::class)
@Preview
@Composable
internal fun CMYSharedElement() {
    var count by remember { mutableStateOf(0) }
    val state = Colors.entries[count.mod(Colors.entries.size)]

    androidx.compose.animation.SharedTransitionLayout(
        modifier = Modifier.clickable {
            count++
        },
    ) {
        com.alexvanyo.composelife.ui.util.AnimatedContent(TargetState.Single(state)) { targetState ->
            when (targetState) {
                Colors.Cyan -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "green"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "blue"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Blue),
                        )
                    }
                }
                Colors.Magenta -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "blue"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Blue),
                        )
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "red"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Red),
                        )
                    }
                }
                Colors.Yellow -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "red"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Red),
                        )
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "green"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Green),
                        )
                    }
                }

                Colors.Red -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "red"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Red),
                        )
                    }
                }
                Colors.Green -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "green"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Green),
                        )
                    }
                }
                Colors.Blue -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "blue"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Blue),
                        )
                    }
                }
                Colors.White -> {
                    Column {
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "red"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Red),
                        )
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "green"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Green),
                        )
                        Box(
                            modifier = Modifier
                                .sharedElementWithCallerManagedVisibility(
                                    rememberSharedContentState(key = "blue"),
                                    targetState == state,
                                )
                                .fillMaxWidth()
                                .weight(1f)
                                .background(Color.Blue),
                        )
                    }
                }
            }
        }
    }
}

enum class Colors {
    Cyan, Magenta, Yellow, Red, Green, Blue, White
}

@Composable
fun ComposableThatFits(
    vararg contents: @Composable ComposableThatFitsScope.() -> Unit,
    modifier: Modifier = Modifier,
) {
    var placedContentIndex by remember(contents) { mutableIntStateOf(-1) }

    val orderedContents = if (placedContentIndex == -1) {
        contents.withIndex()
    } else {
        listOf(IndexedValue(placedContentIndex, contents[placedContentIndex])) +
            contents.withIndex().filter { (index, _) -> index != placedContentIndex }
    }

    Layout(
        content = {
            orderedContents.forEach { (index, content) ->
                content(
                    object : ComposableThatFitsScope {
                        override val isPlaced: Boolean
                            get() = placedContentIndex == -1 || placedContentIndex == index
                    },
                )
            }
        },
        measurePolicy = { measurables, constraints ->
            val measurablesWithIndex = measurables.withIndex()
            val placeable = (
                measurablesWithIndex
                    .firstOrNull { (_, measurable) ->
                        measurable.minIntrinsicWidth(constraints.maxHeight) <= constraints.maxWidth &&
                            measurable.minIntrinsicHeight(constraints.maxWidth) <= constraints.maxHeight
                    } ?: measurablesWithIndex.last()
                )
                .let { (index, measurable) ->
                    placedContentIndex = index
                    measurable.measure(constraints)
                }

            layout(placeable.width, placeable.height) {
                placeable.placeRelative(0, 0)
            }
        },
        modifier = modifier,
    )
}

interface ComposableThatFitsScope {
    val isPlaced: Boolean
}

@Composable
@Preview(widthDp = 400, heightDp = 600)
@Preview(widthDp = 400, heightDp = 500)
@Preview(widthDp = 400, heightDp = 450)
@Preview(widthDp = 400, heightDp = 400)
@Preview(widthDp = 400, heightDp = 350)
@Preview(widthDp = 400, heightDp = 300)
internal fun TextTruncation() {
    Surface {
        Layout(
            content = @Suppress("MaxLineLength", "MaximumLineLength") {
                Text(
                    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.",
                    overflow = TextOverflow.Ellipsis,
                    style = MaterialTheme.typography.titleSmall,
                )
                Text(
                    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.",
                    overflow = TextOverflow.Ellipsis,
                    style = MaterialTheme.typography.bodyMedium,
                )
                Text(
                    "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.",
                    overflow = TextOverflow.Ellipsis,
                    style = MaterialTheme.typography.bodySmall,
                )
            },
            measurePolicy = { measurables, constraints ->
                val minimumIntrinsicSizes = measurables
                    .map { it.minIntrinsicHeight(constraints.maxWidth) }

                // Determine how much space would be need to fit everything up to a certain point at the minimum
                // intrinsic size.
                // Index n of this list refers to the required space to fit measurables 0 to n (inclusive) and
                // fulfill their intrinsic minimum size
                val heightsNeededForMinimumIntrinsicSizes = minimumIntrinsicSizes.runningReduce(Int::plus)

                // Keep track of the remaining height to allocate
                var remainingHeight = constraints.maxHeight

                // Process the measurables in reverse order, as we will take away space from later measurables first.
                val placeables = measurables
                    .withIndex()
                    .reversed()
                    .map { (index, measurable) ->
                        // Determine the single-line height
                        val singleLineHeight = measurable.minIntrinsicHeight(Int.MAX_VALUE)
                        // Retrieve the amount of space needed to fit everything up-to and including this measurable
                        // while fulfilling the minimum intrinsic size
                        val heightNeededForMinimumIntrinsicSizesHere =
                            heightsNeededForMinimumIntrinsicSizes[index]

                        // Determine the maximum height to measure with
                        val maxHeight = if (remainingHeight >= heightNeededForMinimumIntrinsicSizesHere) {
                            // If we have enough space to fit everything completely, just measure with the intrinsic
                            // size
                            minimumIntrinsicSizes[index]
                        } else {
                            // Retrieve the amount of space needed to fit everything up-to but not including this
                            // measurable while fulfilling the minimum intrinsic size
                            val heightNeededForMinimumIntrinsicSizesBefore =
                                heightsNeededForMinimumIntrinsicSizes.getOrElse(index - 1) { 0 }

                            if (remainingHeight >= heightNeededForMinimumIntrinsicSizesBefore + singleLineHeight) {
                                // If we have enough space to fit everything before this measurable, measure this one
                                // with the excess space
                                remainingHeight - heightNeededForMinimumIntrinsicSizesBefore
                            } else {
                                // Otherwise, only allocate this measurable the single-line height
                                singleLineHeight
                            }
                        }

                        val placeable = measurable.measure(constraints.copy(maxHeight = maxHeight))
                        // Remove the allocated height
                        remainingHeight -= placeable.height

                        placeable
                    }
                    .reversed() // Return to top-to-bottom order

                layout(placeables.maxOf(Placeable::width), placeables.sumOf(Placeable::height)) {
                    var y = 0
                    placeables.forEach { placeable ->
                        placeable.placeRelative(0, y)
                        y += placeable.height
                    }
                }
            },
        )
    }
}

@OptIn(ExperimentalSharedTransitionApi::class)
@MobileDevicePreviews
@Preview
@Composable
internal fun MovableContentAnimateAfter() {
    val textField = remember {
        movableContentOf {
            var textFieldValue by rememberSaveable(stateSaver = TextFieldValue.Saver) {
                mutableStateOf(TextFieldValue())
            }
            TextField(
                textFieldValue,
                { textFieldValue = it },
                modifier = Modifier.fillMaxWidth(),
            )
        }
    }

    SharedTransitionScope {
        ComposableThatFits(
            {
                Box(
                    modifier = Modifier
                        .requiredSizeIn(minWidth = 800.dp, minHeight = 400.dp)
                        .fillMaxSize()
                        .background(Color.Yellow),
                    contentAlignment = Alignment.BottomCenter,
                ) {
                    textField()
                }
            },
            {
                Box(
                    modifier = Modifier
                        .requiredSizeIn(minWidth = 400.dp, minHeight = 400.dp)
                        .fillMaxSize()
                        .background(Color.Blue),
                    contentAlignment = Alignment.BottomCenter,
                ) {
                    textField()
                }
            },
            {
                Box(
                    modifier = Modifier
                        .fillMaxSize()
                        .background(Color.Red),
                    contentAlignment = Alignment.BottomCenter,
                ) {
                    textField()
                }
            },
            modifier = it,
        )
    }
}

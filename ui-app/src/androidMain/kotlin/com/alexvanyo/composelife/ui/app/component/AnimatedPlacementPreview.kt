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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.background
import androidx.compose.foundation.border
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Button
import androidx.compose.material3.Slider
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toIntRect
import com.alexvanyo.composelife.ui.util.animateContentSize
import com.alexvanyo.composelife.ui.util.animatePlacement
import com.alexvanyo.composelife.ui.util.bottomEnd
import com.alexvanyo.composelife.ui.util.bottomStart
import com.alexvanyo.composelife.ui.util.centerEnd
import com.alexvanyo.composelife.ui.util.centerStart
import com.alexvanyo.composelife.ui.util.topEnd
import com.alexvanyo.composelife.ui.util.topStart

@Suppress("LongMethod", "CyclomaticComplexMethod")
@Preview
@Composable
fun AnimatePlacementPreview() {
    var animatePlacementAlignmentIndex by remember { mutableStateOf(0) }
    var animatePlacementParentAlignmentIndex by remember { mutableStateOf(0) }
    var alignmentInBoxIndex by remember { mutableStateOf(0) }
    var animateContentSizeAlignmentIndex by remember { mutableStateOf(0) }

    val alignments = listOf(
        "TopStart" to Alignment.TopStart,
        "TopCenter" to Alignment.TopCenter,
        "TopEnd" to Alignment.TopEnd,
        "CenterStart" to Alignment.CenterStart,
        "Center" to Alignment.Center,
        "CenterEnd" to Alignment.CenterEnd,
        "BottomStart" to Alignment.BottomStart,
        "BottomCenter" to Alignment.BottomCenter,
        "BottomEnd" to Alignment.BottomEnd,
    )

    val (animatePlacementAlignmentName, animatePlacementAlignment) =
        alignments[animatePlacementAlignmentIndex.mod(alignments.size)]
    val (animatePlacementParentAlignmentName, animatePlacementParentAlignment) =
        alignments[animatePlacementParentAlignmentIndex.mod(alignments.size)]
    val (alignmentInBoxName, alignmentInBox) =
        alignments[alignmentInBoxIndex.mod(alignments.size)]
    val (animateContentSizeAlignmentName, animateContentSizeAlignment) =
        alignments[animateContentSizeAlignmentIndex.mod(alignments.size)]

    var startFraction by remember { mutableStateOf(0f) }
    var endFraction by remember { mutableStateOf(0f) }
    var topFraction by remember { mutableStateOf(0f) }
    var bottomFraction by remember { mutableStateOf(0f) }

    var isExpanded by remember { mutableStateOf(false) }

    Column {
        Button(
            onClick = { animatePlacementAlignmentIndex++ }
        ) {
            Text("animatePlacement alignment: $animatePlacementAlignmentName")
        }
        Button(
            onClick = { animatePlacementParentAlignmentIndex++ }
        ) {
            Text("animatePlacementParent alignment: $animatePlacementParentAlignmentName")
        }
        Button(
            onClick = { alignmentInBoxIndex++ }
        ) {
            Text("alignment in box: $alignmentInBoxName")
        }
        Button(
            onClick = { animateContentSizeAlignmentIndex++ }
        ) {
            Text("animateContentSize alignment: $animateContentSizeAlignmentName")
        }
        Button(
            onClick = { isExpanded = !isExpanded }
        ) {
            Text("Toggle box size")
        }

        Slider(
            startFraction,
            { startFraction = it },
            valueRange = 0f..0.3f,
        )
        Slider(
            endFraction,
            { endFraction = it },
            valueRange = 0f..0.3f,
        )
        Slider(
            topFraction,
            { topFraction = it },
            valueRange = 0f..0.3f,
        )
        Slider(
            bottomFraction,
            { bottomFraction = it },
            valueRange = 0f..0.3f,
        )

        Row(Modifier.size(400.dp)) {
            Spacer(Modifier.fillMaxWidth(fraction = startFraction))

            Column(Modifier.weight(1f)) {
                Spacer(Modifier.fillMaxHeight(fraction = topFraction))

                Box(
                    Modifier
                        .weight(1f)
                        .fillMaxWidth()
                        .border(1.dp, Color.Red)
                ) {
                    Spacer(
                        Modifier
                            .animatePlacement(
                                fixedPoint = { layoutCoordinates ->
                                    val bounds = layoutCoordinates.boundsInParent()
                                    when (animatePlacementAlignment) {
                                        Alignment.TopStart -> bounds.topStart
                                        Alignment.TopCenter -> bounds.topCenter
                                        Alignment.TopEnd -> bounds.topEnd
                                        Alignment.CenterStart -> bounds.centerStart
                                        Alignment.Center -> bounds.center
                                        Alignment.CenterEnd -> bounds.centerEnd
                                        Alignment.BottomStart -> bounds.bottomStart
                                        Alignment.BottomCenter -> bounds.bottomCenter
                                        Alignment.BottomEnd -> bounds.bottomEnd
                                        else -> error("invalid alignment")
                                    }.round()
                                },
                                parentFixedPoint = { parentLayoutCoordinates ->
                                    val bounds = parentLayoutCoordinates.size.toIntRect()
                                    when (animatePlacementParentAlignment) {
                                        Alignment.TopStart -> bounds.topStart
                                        Alignment.TopCenter -> bounds.topCenter
                                        Alignment.TopEnd -> bounds.topEnd
                                        Alignment.CenterStart -> bounds.centerStart
                                        Alignment.Center -> bounds.center
                                        Alignment.CenterEnd -> bounds.centerEnd
                                        Alignment.BottomStart -> bounds.bottomStart
                                        Alignment.BottomCenter -> bounds.bottomCenter
                                        Alignment.BottomEnd -> bounds.bottomEnd
                                        else -> error("invalid alignment")
                                    }
                                }
                            )
                            .align(alignmentInBox)
                            .background(Color.Blue)
                            .animateContentSize(alignment = animateContentSizeAlignment)
                            .size(if (isExpanded) 128.dp else 64.dp)
                    )
                }

                Spacer(Modifier.fillMaxHeight(fraction = bottomFraction))
            }

            Spacer(Modifier.fillMaxWidth(fraction = endFraction))
        }
    }
}

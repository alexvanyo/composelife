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

@file:Suppress("UnusedPrivateMemeber")

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.Slider
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.asComposePath
import androidx.compose.ui.graphics.drawscope.scale
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import androidx.graphics.shapes.CornerRounding
import androidx.graphics.shapes.RoundedPolygon
import androidx.graphics.shapes.toPath
import com.alexvanyo.composelife.ui.util.hatTurtleTile
import kotlin.math.sqrt

@Preview
@Composable
private fun ChevronPreview() {
    val shape = RoundedPolygon.hatTurtleTile(0f, sqrt(3f), emptyList()).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun HatPreview() {
    val shape = RoundedPolygon.hatTurtleTile(1f, sqrt(3f), emptyList()).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun SpectrePreviewS() {
    val shape = RoundedPolygon.hatTurtleTile(
        1f,
        1f,
        listOf(
            Offset(0.25f, 0.25f) to CornerRounding(0.25f, 1f),
            Offset(0.5f, 0f) to CornerRounding.Unrounded,
            Offset(0.75f, -0.25f) to CornerRounding(0.25f, 1f),
        ),
    ).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun SpectrePreviewCurve() {
    val shape = RoundedPolygon.hatTurtleTile(
        1f,
        1f,
        listOf(
            Offset(1f / 3f, -0.25f) to CornerRounding(0.5f, 1f),
        ),
    ).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun SpectrePreviewUnrounded() {
    val shape = RoundedPolygon.hatTurtleTile(1f, 1f, emptyList()).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun TurtlePreview() {
    val shape = RoundedPolygon.hatTurtleTile(sqrt(3f), 1f, emptyList()).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@Preview
@Composable
private fun CometPreview() {
    val shape = RoundedPolygon.hatTurtleTile(sqrt(3f), 0f, emptyList()).normalized().toPath().asComposePath()

    Canvas(modifier = Modifier
        .size(100.dp)
        .background(Color.Black)) {
        scale(size.minDimension, pivot = Offset.Zero) {
            drawPath(shape, Color.White)
        }
    }
}

@OptIn(ExperimentalLayoutApi::class)
@Preview
@Composable
private fun HatTurtleContinuumPreview() {
    var a by remember { mutableFloatStateOf(1f) }
    var b by remember { mutableFloatStateOf(sqrt(3f)) }
    var curve by remember { mutableFloatStateOf(0f) }

    val shape = RoundedPolygon.hatTurtleTile(
        a = a,
        b = b,
        segmentCurve = listOf(
            Offset(0.25f, curve) to CornerRounding(0.25f, 1f),
            Offset(0.5f, 0f) to CornerRounding.Unrounded,
            Offset(0.75f, -curve) to CornerRounding(0.25f, 1f),
        ),
    ).normalized().toPath().asComposePath()

    Column(
        horizontalAlignment = Alignment.CenterHorizontally,
        modifier = Modifier.verticalScroll(rememberScrollState())
    ) {
        Slider(
            value = a,
            valueRange = 0f..2f,
            onValueChange = { a = it },
        )
        Slider(
            value = b,
            valueRange = 0f..2f,
            onValueChange = { b = it },
        )
        Slider(
            value = curve,
            valueRange = 0f..1f,
            onValueChange = { curve = it },
        )

        Canvas(
            modifier = Modifier
                .size(400.dp)
                .aspectRatio(1f, matchHeightConstraintsFirst = true)
                .background(Color.Black)
        ) {
            scale(size.minDimension, pivot = Offset.Zero) {
                drawPath(shape, Color.White)
            }
        }
    }
}

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

import androidx.compose.ui.geometry.Offset
import androidx.graphics.shapes.CornerRounding
import androidx.graphics.shapes.RoundedPolygon
import kotlin.math.cos
import kotlin.math.sin

/**
 * Creates a [RoundedPolygon] representing the shape for a tile on the hat-turtle continuum.
 *
 * Members of this family of shapes can tile the plane aperiodically.
 *
 * [a] and [b] control the side lengths, [segmentCurve] can create a curve on each line segment, by specifying a list
 * of intermediate points between (0, 0) and (1, 0) paired with a given [CornerRounding].
 *
 * "hat", "spectre" and "turtle" can be constructed with the following:
 * - hatTurtleTile(1, sqrt(3)) creates the "hat"
 * - hatTurtleTile(1, 1) creates the "spectre"
 * - hatTurtleTile(1, 1, listOf(Offset(1f / 3f, -0.25f) to CornerRounding(0.5f, 1f))) creates the "spectre" that only
 *   admits non-periodic tilings even when reflections are permitted.
 * - hatTurtleTile(sqrt(3), 1) creates the "turtle"
 *
 * The returned shape is not normalized. Use [RoundedPolygon.normalized] to normalize the size.
 */
fun RoundedPolygon.Companion.hatTurtleTile(
    a: Float,
    b: Float,
    segmentCurve: List<Pair<Offset, CornerRounding>> = emptyList(),
): RoundedPolygon {
    val c = cos(FloatPi / 3f)
    val s = sin(FloatPi / 3f)
    val moves = listOf(
        Offset(c * b, s * b),
        Offset(b, 0f),
        Offset(0f, a),
        Offset(s * a, c * a),
        Offset(c * b, -s * b),
        Offset(-c * b, -s * b),
        Offset(s * a, -c * a),
        Offset(0f, -a),
        Offset(0f, -a),
        Offset(-s * a, -c * a),
        Offset(-c * b, s * b),
        Offset(-b, 0f),
        Offset(0f, a),
        Offset(-s * a, c * a),
    )
        // Remove any moves that aren't actually moves in the degenerate case
        .filter { it.getDistanceSquared() != 0f }
    val segmentCurveVertices = segmentCurve.map(Pair<Offset, CornerRounding>::first)
    val segmentCurveCornerRoundings = segmentCurve.map(Pair<Offset, CornerRounding>::second)

    // Compute the list of corner roundings based on the segment curve
    val perVertexRounding = listOf(b, b, a, a, b, b, a, a, a, a, b, b, a, a)
        // Remove any moves that aren't actually moves in the degenerate case
        .filter { it != 0f }
        .flatMapIndexed { index, sideLength ->
            // To preserve chirality, the curve for every other edge needs to be rotated 180 degrees
            val rotatedSegmentCurveCornerRoundings = if (index.mod(2) == 0) {
                segmentCurveCornerRoundings
            } else {
                segmentCurveCornerRoundings.reversed()
            }

            listOf(CornerRounding.Unrounded) + rotatedSegmentCurveCornerRoundings.map { segmentCornerRounding ->
                CornerRounding(radius = segmentCornerRounding.radius * sideLength, segmentCornerRounding.smoothing)
            }
        }

    val vertices = buildList {
        var current = Offset.Zero
        add(current)
        moves.forEachIndexed { index, move ->
            val normal = Offset(-move.y, move.x)

            // To preserve chirality, the curve for every other edge needs to be rotated 180 degrees
            val rotatedSegmentCurveVertices = if (index.mod(2) == 0) {
                segmentCurveVertices
            } else {
                segmentCurveVertices.map { segmentVertex ->
                    Offset(x = 1 - segmentVertex.x, y = -segmentVertex.y)
                }.reversed()
            }
            rotatedSegmentCurveVertices.forEach { segmentVertex ->
                add(current + move * segmentVertex.x + normal * segmentVertex.y)
            }

            add(current + move)
            current += move
        }
    }
        .dropLast(1) // Remove the last point, which is the same as the start point

    return RoundedPolygon(
        vertices = vertices
            .map { listOf(it.x, it.y) }
            .flatten()
            .toFloatArray(),
        perVertexRounding = perVertexRounding,
        centerX = (vertices.maxOf(Offset::x) - vertices.minOf(Offset::x)) / 2f,
        centerY = (vertices.maxOf(Offset::y) - vertices.minOf(Offset::y)) / 2f,
    )
}

private const val FloatPi = Math.PI.toFloat()

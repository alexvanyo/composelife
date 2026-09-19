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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset

/**
 * Converts an [IntOffset] to a [CellCoordinate].
 */
fun IntOffset.toCellCoordinate(): CellCoordinate = CellCoordinate(packedValue)

/**
 * Converts a [CellCoordinate] to an [IntOffset].
 */
fun CellCoordinate.toIntOffset(): IntOffset = IntOffset(packedValue)

/**
 * Converts a set of [IntOffset]s to a set of [CellCoordinate]s.
 */
@Suppress("UNCHECKED_CAST")
fun Set<IntOffset>.toCellCoordinates(): Set<CellCoordinate> = this as Set<CellCoordinate>

/**
 * Converts a set of [CellCoordinate]s to a set of [IntOffset]s.
 */
@Suppress("UNCHECKED_CAST")
fun Set<CellCoordinate>.toIntOffsets(): Set<IntOffset> = this as Set<IntOffset>

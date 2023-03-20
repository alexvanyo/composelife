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
@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.ui.util

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.LayoutDirection

fun Rect.topStart(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> topLeft
    LayoutDirection.Rtl -> topRight
}

fun Rect.topEnd(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> topRight
    LayoutDirection.Rtl -> topLeft
}

fun Rect.centerStart(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> centerLeft
    LayoutDirection.Rtl -> centerRight
}

fun Rect.centerEnd(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> centerRight
    LayoutDirection.Rtl -> centerLeft
}

fun Rect.bottomStart(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> bottomLeft
    LayoutDirection.Rtl -> bottomRight
}

fun Rect.bottomEnd(layoutDirection: LayoutDirection): Offset = when (layoutDirection) {
    LayoutDirection.Ltr -> bottomRight
    LayoutDirection.Rtl -> bottomLeft
}

fun IntRect.topStart(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> topLeft
    LayoutDirection.Rtl -> topRight
}

fun IntRect.topEnd(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> topRight
    LayoutDirection.Rtl -> topLeft
}

fun IntRect.centerStart(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> centerLeft
    LayoutDirection.Rtl -> centerRight
}

fun IntRect.centerEnd(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> centerRight
    LayoutDirection.Rtl -> centerLeft
}

fun IntRect.bottomStart(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> bottomLeft
    LayoutDirection.Rtl -> bottomRight
}

fun IntRect.bottomEnd(layoutDirection: LayoutDirection): IntOffset = when (layoutDirection) {
    LayoutDirection.Ltr -> bottomRight
    LayoutDirection.Rtl -> bottomLeft
}

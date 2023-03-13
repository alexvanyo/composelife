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

package com.alexvanyo.composelife.ui.util

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.LayoutDirection

context(LayoutDirection)
val Rect.topStart get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> topLeft
    LayoutDirection.Rtl -> topRight
}

context(LayoutDirection)
val Rect.topEnd get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> topRight
    LayoutDirection.Rtl -> topLeft
}

context(LayoutDirection)
val Rect.centerStart get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> centerLeft
    LayoutDirection.Rtl -> centerRight
}

context(LayoutDirection)
val Rect.centerEnd get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> centerRight
    LayoutDirection.Rtl -> centerLeft
}

context(LayoutDirection)
val Rect.bottomStart get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> bottomLeft
    LayoutDirection.Rtl -> bottomRight
}

context(LayoutDirection)
val Rect.bottomEnd get(): Offset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> bottomRight
    LayoutDirection.Rtl -> bottomLeft
}

context(LayoutDirection)
val IntRect.topStart get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> topLeft
    LayoutDirection.Rtl -> topRight
}

context(LayoutDirection)
val IntRect.topEnd get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> topRight
    LayoutDirection.Rtl -> topLeft
}

context(LayoutDirection)
val IntRect.centerStart get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> centerLeft
    LayoutDirection.Rtl -> centerRight
}

context(LayoutDirection)
val IntRect.centerEnd get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> centerRight
    LayoutDirection.Rtl -> centerLeft
}

context(LayoutDirection)
val IntRect.bottomStart get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> bottomLeft
    LayoutDirection.Rtl -> bottomRight
}

context(LayoutDirection)
val IntRect.bottomEnd get(): IntOffset = when (this@LayoutDirection) {
    LayoutDirection.Ltr -> bottomRight
    LayoutDirection.Rtl -> bottomLeft
}

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
import com.alexvanyo.composelife.geometry.bottomEnd
import com.alexvanyo.composelife.geometry.bottomStart
import com.alexvanyo.composelife.geometry.centerEnd
import com.alexvanyo.composelife.geometry.centerStart
import com.alexvanyo.composelife.geometry.topEnd
import com.alexvanyo.composelife.geometry.topStart

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.topStart get(): Offset = topStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.topEnd get(): Offset = topEnd(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.centerStart get(): Offset = centerStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.centerEnd get(): Offset = centerEnd(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.bottomStart get(): Offset = bottomStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val Rect.bottomEnd get(): Offset = bottomEnd(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.topStart get(): IntOffset = topStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.topEnd get(): IntOffset = topEnd(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.centerStart get(): IntOffset = centerStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.centerEnd get(): IntOffset = centerEnd(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.bottomStart get(): IntOffset = bottomStart(layoutDirectionAwareScope.layoutDirection)

context(layoutDirectionAwareScope: LayoutDirectionAwareScope)
val IntRect.bottomEnd get(): IntOffset = bottomEnd(layoutDirectionAwareScope.layoutDirection)

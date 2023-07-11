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

package com.alexvanyo.composelife.ui.app.info

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.app.R

actual fun OffsetInfoMessage(x: Float, y: Float): ParameterizedString =
    ParameterizedString(R.string.offset, x, y)

actual fun ScaleInfoMessage(scale: Float): ParameterizedString =
    ParameterizedString(R.string.scale, scale)

actual fun PausedMessage(): ParameterizedString =
    ParameterizedString(R.string.paused)

actual fun GenerationsPerSecondShortMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString(R.string.generations_per_second_short, generationsPerSecond)

actual fun GenerationsPerSecondLongMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString(R.string.generations_per_second_long, generationsPerSecond)

actual fun CollapseMessage(): ParameterizedString =
    ParameterizedString(R.string.collapse)

actual fun ExpandMessage(): ParameterizedString =
    ParameterizedString(R.string.expand)

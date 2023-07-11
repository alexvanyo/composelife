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

actual fun OffsetInfoMessage(x: Float, y: Float): ParameterizedString =
    ParameterizedString("Offset: x = %.1f, y = %.1f".format(x, y))

actual fun ScaleInfoMessage(scale: Float): ParameterizedString =
    ParameterizedString("Scale: %.2f".format(scale))

actual fun PausedMessage(): ParameterizedString =
    ParameterizedString("Paused")

actual fun GenerationsPerSecondShortMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("GPS: %.2f".format(generationsPerSecond))

actual fun GenerationsPerSecondLongMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("Generations per second: %.2f".format(generationsPerSecond))

actual fun CollapseMessage(): ParameterizedString =
    ParameterizedString("Collapse")

actual fun ExpandMessage(): ParameterizedString =
    ParameterizedString("Expand")

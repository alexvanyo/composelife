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

package com.alexvanyo.composelife.ui.app.action

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.app.R

actual fun TargetStepsPerSecondLabelAndValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString(R.string.target_steps_per_second_label_and_value, targetStepsPerSecond)

actual fun TargetStepsPerSecondValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString(R.string.target_steps_per_second_value, targetStepsPerSecond)

actual fun TargetStepsPerSecondLabel(): ParameterizedString =
    ParameterizedString(R.string.target_steps_per_second_label)

actual fun GenerationsPerStepLabelAndValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString(R.string.generations_per_step_label_and_value, generationsPerStep)

actual fun GenerationsPerStepValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString(R.string.generations_per_step_value, generationsPerStep)

actual fun GenerationsPerStepLabel(): ParameterizedString =
    ParameterizedString(R.string.generations_per_step_label)

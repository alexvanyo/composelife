/*
 * Copyright 2022 The Android Open Source Project
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
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

expect fun UnexpectedInputMessage(
    input: String,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString

expect fun UnexpectedCharacterMessage(
    character: Char,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString

expect fun UnexpectedHeaderMessage(
    header: String,
): ParameterizedString

expect fun UnexpectedShortLineMessage(
    lineIndex: Int,
): ParameterizedString

expect fun UnexpectedBlankLineMessage(
    lineIndex: Int,
): ParameterizedString

expect val UnexpectedEmptyFileMessage: ParameterizedString

expect val RuleNotSupportedMessage: ParameterizedString

expect fun DuplicateTopLeftCoordinateMessage(
    overwritingOffset: IntOffset,
): ParameterizedString

expect val EmptyInput: ParameterizedString

expect fun UnexpectedNodeIdMessage(
    lineIndex: Int,
    characterIndices: IntRange,
): ParameterizedString

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

import com.alexvanyo.composelife.algorithm.R
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

actual fun UnexpectedInputMessage(
    input: String,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_input,
    input,
    lineIndex,
    characterIndex,
)

actual fun UnexpectedCharacterMessage(
    character: Char,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_character,
    character,
    lineIndex,
    characterIndex,
)

actual fun UnexpectedHeaderMessage(
    header: String,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_header,
    header,
)

actual fun UnexpectedShortLineMessage(
    lineIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_short_line,
    lineIndex,
)

actual fun UnexpectedBlankLineMessage(
    lineIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_blank_line,
    lineIndex,
)

actual fun UnexpectedEmptyFileMessage(): ParameterizedString =
    ParameterizedString(R.string.unexpected_empty_file)

actual fun RuleNotSupportedMessage(): ParameterizedString =
    ParameterizedString(R.string.rule_not_supported)

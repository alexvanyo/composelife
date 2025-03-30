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
import com.alexvanyo.composelife.algorithm.R
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.ParameterizedStringArgument

actual fun UnexpectedInputMessage(
    input: String,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_input,
    ParameterizedStringArgument(input),
    ParameterizedStringArgument(lineIndex),
    ParameterizedStringArgument(characterIndex),
)

actual fun UnexpectedCharacterMessage(
    character: Char,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_character,
    ParameterizedStringArgument(character),
    ParameterizedStringArgument(lineIndex),
    ParameterizedStringArgument(characterIndex),
)

actual fun UnexpectedHeaderMessage(
    header: String,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_header,
    ParameterizedStringArgument(header),
)

actual fun UnexpectedShortLineMessage(
    lineIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_short_line,
    ParameterizedStringArgument(lineIndex),
)

actual fun UnexpectedBlankLineMessage(
    lineIndex: Int,
): ParameterizedString = ParameterizedString(
    R.string.unexpected_blank_line,
    ParameterizedStringArgument(lineIndex),
)

actual val UnexpectedEmptyFileMessage: ParameterizedString =
    ParameterizedString(R.string.unexpected_empty_file)

actual val RuleNotSupportedMessage: ParameterizedString =
    ParameterizedString(R.string.rule_not_supported)

actual fun DuplicateTopLeftCoordinateMessage(
    overwritingOffset: IntOffset,
): ParameterizedString =
    ParameterizedString(
        R.string.duplicate_top_left_coordinate,
        ParameterizedStringArgument(overwritingOffset.x),
        ParameterizedStringArgument(overwritingOffset.y),
    )

actual val EmptyInput: ParameterizedString =
    ParameterizedString(R.string.empty_input)

actual fun UnexpectedNodeIdMessage(
    lineIndex: Int,
    characterIndices: IntRange,
): ParameterizedString =
    ParameterizedString(
        R.string.unexpected_node_id,
        ParameterizedStringArgument(lineIndex),
        ParameterizedStringArgument(characterIndices.first),
        ParameterizedStringArgument(characterIndices.last),
    )

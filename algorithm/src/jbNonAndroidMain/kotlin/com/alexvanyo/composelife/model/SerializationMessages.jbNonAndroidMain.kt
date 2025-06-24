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
import com.alexvanyo.composelife.parameterizedstring.ParameterizedStringArgument

actual fun UnexpectedInputMessage(
    input: String,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString =
    ParameterizedString(
        "Unexpected input \"%s\" starting on line %d, character %d",
        ParameterizedStringArgument(input),
        ParameterizedStringArgument(lineIndex),
        ParameterizedStringArgument(characterIndex),
    )

actual fun UnexpectedCharacterMessage(
    character: Char,
    lineIndex: Int,
    characterIndex: Int,
): ParameterizedString =
    ParameterizedString(
        "Unexpected character %c on line %d, offset %d interpreted as on",
        ParameterizedStringArgument(character),
        ParameterizedStringArgument(lineIndex),
        ParameterizedStringArgument(characterIndex),
    )

actual fun UnexpectedHeaderMessage(
    header: String,
): ParameterizedString =
    ParameterizedString("Unexpected header, found %s", ParameterizedStringArgument(header))

actual fun UnexpectedShortLineMessage(
    lineIndex: Int,
): ParameterizedString =
    ParameterizedString("Line %dx is unexpectedly short", ParameterizedStringArgument(lineIndex))

actual fun UnexpectedBlankLineMessage(
    lineIndex: Int,
): ParameterizedString =
    ParameterizedString("Unexpected blank line at line %d", ParameterizedStringArgument(lineIndex))

actual val UnexpectedEmptyFileMessage: ParameterizedString =
    ParameterizedString("Unexpected empty file, assuming blank pattern")

actual val RuleNotSupportedMessage: ParameterizedString =
    ParameterizedString("Ruleset not supported")

actual fun DuplicateTopLeftCoordinateMessage(
    overwritingOffset: IntOffset,
): ParameterizedString =
    ParameterizedString(
        "Duplicate top-left coordinate instruction, overwriting with (%d, %d)",
        ParameterizedStringArgument(overwritingOffset.x),
        ParameterizedStringArgument(overwritingOffset.y),
    )

actual val EmptyInput: ParameterizedString =
    ParameterizedString("Input was empty, could not parse")

actual fun UnexpectedNodeIdMessage(
    lineIndex: Int,
    characterIndices: IntRange,
): ParameterizedString =
    ParameterizedString(
        "Invalid node id on line %d, characters %d-%d",
        ParameterizedStringArgument(lineIndex),
        ParameterizedStringArgument(characterIndices.first),
        ParameterizedStringArgument(characterIndices.last),
    )

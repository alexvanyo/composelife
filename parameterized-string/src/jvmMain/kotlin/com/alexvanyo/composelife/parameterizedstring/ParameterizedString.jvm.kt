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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.parameterizedstring

import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.runtime.saveable.Saver
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.serialization.saver
import kotlinx.serialization.Serializable

@Serializable
expect sealed class ParameterizedString {
    companion object
}

/**
 * Creates a representation of a plain-text string.
 */
expect fun ParameterizedString(
    value: String,
    vararg args: ParameterizedStringArgument,
): ParameterizedString

@Serializable
sealed interface ParameterizedStringArgument {
    @Serializable
    data class ParameterizedStringArg(val value: ParameterizedString) : ParameterizedStringArgument

    @Serializable
    data class StringArg(val value: String) : ParameterizedStringArgument

    @Serializable
    data class IntArg(val value: Int) : ParameterizedStringArgument

    @Serializable
    data class CharArg(val value: Char) : ParameterizedStringArgument

    @Serializable
    data class FloatArg(val value: Float) : ParameterizedStringArgument

    @Serializable
    data class DoubleArg(val value: Double) : ParameterizedStringArgument
}

fun ParameterizedStringArgument(value: ParameterizedString): ParameterizedStringArgument =
    ParameterizedStringArgument.ParameterizedStringArg(value)
fun ParameterizedStringArgument(value: String): ParameterizedStringArgument =
    ParameterizedStringArgument.StringArg(value)
fun ParameterizedStringArgument(value: Int): ParameterizedStringArgument =
    ParameterizedStringArgument.IntArg(value)
fun ParameterizedStringArgument(value: Char): ParameterizedStringArgument =
    ParameterizedStringArgument.CharArg(value)
fun ParameterizedStringArgument(value: Float): ParameterizedStringArgument =
    ParameterizedStringArgument.FloatArg(value)
fun ParameterizedStringArgument(value: Double): ParameterizedStringArgument =
    ParameterizedStringArgument.DoubleArg(value)

val ParameterizedString.Companion.Saver: Saver<ParameterizedString, SavedState> get() = serializer().saver()

/**
 * Creates a lambda to resolve the [ParameterizedString] to a [String].
 */
@Composable
expect fun parameterizedStringResolver(): (ParameterizedString) -> String

/**
 * Resolves the [ParameterizedString] to a [String].
 */
@Composable
@ReadOnlyComposable
expect fun parameterizedStringResource(parameterizedString: ParameterizedString): String

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

package com.alexvanyo.composelife.parameterizedstring

import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.text.intl.Locale

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Context].
 */
fun getParameterizedString(locale: Locale, parameterizedString: ParameterizedString): String {
    val resolvedArgs = parameterizedString.args.map { arg ->
        when (arg) {
            is ParameterizedString -> getParameterizedString(locale, arg)
            else -> arg
        }
    }.toTypedArray()

    return when (parameterizedString) {
        is ParameterizedString.BasicString -> {
            @Suppress("SpreadOperator")
            parameterizedString.value.format(
                locale = java.util.Locale.forLanguageTag(locale.toLanguageTag()),
                *resolvedArgs,
            )
        }
    }
}

/**
 * Creates a lambda to resolve the [ParameterizedString] to a [String].
 */
@Composable
actual fun parameterizedStringResolver(): (ParameterizedString) -> String {
    val locale = Locale.current
    return {
        getParameterizedString(locale, it)
    }
}

/**
 * Resolves the [ParameterizedString] to a [String] using the local [Context].
 */
@Composable
@ReadOnlyComposable
actual fun parameterizedStringResource(parameterizedString: ParameterizedString): String =
    getParameterizedString(Locale.current, parameterizedString)

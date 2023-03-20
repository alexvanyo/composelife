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

import android.content.Context
import android.content.res.Resources
import androidx.annotation.PluralsRes
import androidx.annotation.StringRes
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext

/**
 * A nestable representation of a string resource or a quantity string resource.
 */
actual sealed class ParameterizedString {
    internal abstract val args: List<Any>

    internal data class NormalString(
        @StringRes val stringRes: Int,
        override val args: List<Any>,
    ) : ParameterizedString()

    internal data class QuantityString(
        @PluralsRes val pluralsRes: Int,
        val quantity: Int,
        override val args: List<Any>,
    ) : ParameterizedString()
}

/**
 * Creates a representation of a string resource [stringRes] with optional [args].
 */
fun ParameterizedString(
    @StringRes stringRes: Int,
    vararg args: Any,
): ParameterizedString = ParameterizedString.NormalString(
    stringRes = stringRes,
    args = args.toList(),
)

/**
 * Creates a representation of a quantity string resource [pluralsRes] with [quantity] and optional [args].
 */
fun ParameterizedQuantityString(
    @PluralsRes pluralsRes: Int,
    quantity: Int,
    vararg args: Any,
): ParameterizedString = ParameterizedString.QuantityString(
    pluralsRes = pluralsRes,
    quantity = quantity,
    args = args.toList(),
)

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Context].
 */
fun Context.getParameterizedString(parameterizedString: ParameterizedString): String =
    resources.getParameterizedString(parameterizedString)

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Resources].
 */
fun Resources.getParameterizedString(parameterizedString: ParameterizedString): String {
    val resolvedArgs = parameterizedString.args.map { arg ->
        when (arg) {
            is ParameterizedString -> getParameterizedString(arg)
            else -> arg
        }
    }.toTypedArray()

    return when (parameterizedString) {
        is ParameterizedString.NormalString -> {
            @Suppress("SpreadOperator")
            getString(
                parameterizedString.stringRes,
                *resolvedArgs,
            )
        }
        is ParameterizedString.QuantityString -> {
            @Suppress("SpreadOperator")
            getQuantityString(
                parameterizedString.pluralsRes,
                parameterizedString.quantity,
                *resolvedArgs,
            )
        }
    }
}

/**
 * Creates a lambda to resolve the [ParameterizedString] to a [String].
 */
@Composable
fun parameterizedStringResolver(): (ParameterizedString) -> String {
    LocalConfiguration.current
    val context = LocalContext.current
    return {
        context.getParameterizedString(it)
    }
}

/**
 * Resolves the [ParameterizedString] to a [String] using the local [Context].
 */
@Composable
@ReadOnlyComposable
actual fun parameterizedStringResource(parameterizedString: ParameterizedString): String {
    LocalConfiguration.current
    return LocalContext.current.getParameterizedString(parameterizedString)
}

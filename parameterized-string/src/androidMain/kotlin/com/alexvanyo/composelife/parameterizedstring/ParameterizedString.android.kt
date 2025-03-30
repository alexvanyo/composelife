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

import android.content.Context
import androidx.annotation.PluralsRes
import androidx.annotation.StringRes
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.core.os.ConfigurationCompat
import kotlinx.serialization.Serializable

/**
 * A nestable representation of a string resource or a quantity string resource.
 */
@Serializable
actual sealed class ParameterizedString {

    internal abstract val args: List<ParameterizedStringArgument>

    @Serializable
    internal data class NormalString(
        @field:StringRes
        @param:StringRes
        val stringRes: Int,
        override val args: List<ParameterizedStringArgument>,
    ) : ParameterizedString()

    @Serializable
    internal data class QuantityString(
        @field:PluralsRes
        @param:PluralsRes
        val pluralsRes: Int,
        val quantity: Int,
        override val args: List<ParameterizedStringArgument>,
    ) : ParameterizedString()

    @Serializable
    internal data class BasicString(
        val value: String,
        override val args: List<ParameterizedStringArgument>,
    ) : ParameterizedString()

    actual companion object
}

/**
 * Creates a representation of a plain-text string.
 */
actual fun ParameterizedString(
    value: String,
    vararg args: ParameterizedStringArgument,
): ParameterizedString = ParameterizedString.BasicString(value, args.toList())

/**
 * Creates a representation of a string resource [stringRes] with optional [args].
 */
fun ParameterizedString(
    @StringRes stringRes: Int,
    vararg args: ParameterizedStringArgument,
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
    vararg args: ParameterizedStringArgument,
): ParameterizedString = ParameterizedString.QuantityString(
    pluralsRes = pluralsRes,
    quantity = quantity,
    args = args.toList(),
)

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Context].
 */
fun Context.getParameterizedString(parameterizedString: ParameterizedString): String {
    val resolvedArgs = parameterizedString.args.map { arg ->
        when (arg) {
            is ParameterizedStringArgument.FloatArg -> arg.value
            is ParameterizedStringArgument.DoubleArg -> arg.value
            is ParameterizedStringArgument.IntArg -> arg.value
            is ParameterizedStringArgument.CharArg -> arg.value
            is ParameterizedStringArgument.ParameterizedStringArg -> getParameterizedString(arg.value)
            is ParameterizedStringArgument.StringArg -> arg.value
        }
    }.toTypedArray<Any>()

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
            resources.getQuantityString(
                parameterizedString.pluralsRes,
                parameterizedString.quantity,
                *resolvedArgs,
            )
        }
        is ParameterizedString.BasicString -> {
            @Suppress("SpreadOperator")
            parameterizedString.value.format(
                locale = ConfigurationCompat.getLocales(resources.configuration)[0],
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

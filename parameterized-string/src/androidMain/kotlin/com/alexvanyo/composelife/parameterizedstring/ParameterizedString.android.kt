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
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext
import androidx.core.os.ConfigurationCompat

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

    internal data class BasicString(
        val value: String,
        override val args: List<Any>,
    ) : ParameterizedString()

    actual companion object
}

actual val ParameterizedString.Companion.Saver: Saver<ParameterizedString, Any> get() =
    listSaver(
        save = { save(it) },
        restore = { restore(it) },
    )

private fun save(parameterizedString: ParameterizedString): List<Any> =
    when (parameterizedString) {
        is ParameterizedString.NormalString -> listOf(
            0,
            parameterizedString.stringRes,
        )
        is ParameterizedString.QuantityString -> listOf(
            1,
            parameterizedString.pluralsRes,
            parameterizedString.quantity,
        )
        is ParameterizedString.BasicString -> listOf(
            2,
            parameterizedString.value,
        )
    } + parameterizedString.args.map { arg ->
        when (arg) {
            is ParameterizedString -> listOf(
                0,
                save(arg),
            )
            else -> listOf(
                1,
                arg,
            )
        }
    }

private fun restore(list: List<Any>): ParameterizedString {
    val type = list[0] as Int

    @Suppress("UNCHECKED_CAST")
    val args = list.drop(
        when (type) {
            0 -> 2
            1 -> 3
            2 -> 2
            else -> error("Unexpected type $type")
        },
    ) as List<List<Any>>
    val restoredArgs = args.map { arg ->
        val argType = arg[0] as Int
        when (argType) {
            0 ->
                @Suppress("UNCHECKED_CAST")
                restore(arg[1] as List<Any>)
            1 -> arg[1]
            else -> error("Unexpected type $argType")
        }
    }

    return when (type) {
        0 -> {
            ParameterizedString.NormalString(
                list[1] as Int,
                restoredArgs,
            )
        }
        1 -> {
            ParameterizedString.QuantityString(
                list[1] as Int,
                list[2] as Int,
                restoredArgs,
            )
        }
        2 -> {
            ParameterizedString.BasicString(
                list[1] as String,
                restoredArgs,
            )
        }
        else -> error("Unexpected type $type")
    }
}

/**
 * Creates a representation of a plain-text string.
 */
actual fun ParameterizedString(
    value: String,
    vararg args: Any,
): ParameterizedString = ParameterizedString.BasicString(value, args.toList())

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
fun Context.getParameterizedString(parameterizedString: ParameterizedString): String {
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

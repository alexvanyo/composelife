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
import androidx.annotation.StringRes
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext

/**
 * A nestable representation of a [stringRes] with optional formatting arguments [args].
 *
 * [args] can be empty, or contain other [ParameterizedString]s (in which case resolution will be recursive).
 */
data class ParameterizedString(
    @StringRes val stringRes: Int,
    val args: List<Any>,
) {
    /**
     * A convenience varargs constructor.
     */
    constructor(
        @StringRes stringRes: Int,
        vararg args: Any,
    ) : this(
        stringRes = stringRes,
        args = args.toList()
    )
}

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

    @Suppress("SpreadOperator")
    return getString(
        parameterizedString.stringRes,
        *resolvedArgs
    )
}

/**
 * Resolves the [ParameterizedString] to a [String] using the local [Context].
 */
@Composable
@ReadOnlyComposable
fun parameterizedStringResource(parameterizedString: ParameterizedString): String {
    LocalConfiguration.current
    return LocalContext.current.getParameterizedString(parameterizedString)
}

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
            is ParameterizedStringArgument.FloatArg -> arg.value
            is ParameterizedStringArgument.DoubleArg -> arg.value
            is ParameterizedStringArgument.IntArg -> arg.value
            is ParameterizedStringArgument.CharArg -> arg.value
            is ParameterizedStringArgument.ParameterizedStringArg -> getParameterizedString(locale, arg.value)
            is ParameterizedStringArgument.StringArg -> arg.value
        }
    }.toTypedArray<Any>()

    return when (parameterizedString) {
        is ParameterizedString.BasicString -> {
            var searchIndex = 0
            var argIndex = 0
            var usingParameterIndex = false
            val formatRegex = Regex("""(.*)(%(\d+n)?[0 #+-]?[0-9*]*\.?\d*[hl]{0,2}[jztL]?([diuoxXeEfgGaAcpsSn%]))""")
            buildString {
                while (searchIndex < parameterizedString.value.length) {
                    val nextMatch = formatRegex.matchAt(parameterizedString.value, searchIndex)
                    if (nextMatch == null) {
                        append(parameterizedString.value.substring(searchIndex))
                        searchIndex = parameterizedString.value.length
                    } else {
                        val beforeFormat = nextMatch.groups[1]
                        val entireFormat = nextMatch.groups[2]
                        val parameterIndex = nextMatch.groups[3]
                        val formatType = nextMatch.groups[4]
                        append(beforeFormat)
                        if (formatType!!.value == "%") {
                            append("%")
                        } else if (parameterIndex == null) {
                            require(!usingParameterIndex) {
                                "Argument $entireFormat didn't have parameter index but came after one that did!"
                            }
                            append(resolvedArgs[argIndex])
                            argIndex++
                        } else {
                            usingParameterIndex = true
                            append(resolvedArgs[parameterIndex.value.dropLast(1).toInt()])
                        }
                        searchIndex += nextMatch.groups[5]!!.value.length
                    }
                }
            }
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

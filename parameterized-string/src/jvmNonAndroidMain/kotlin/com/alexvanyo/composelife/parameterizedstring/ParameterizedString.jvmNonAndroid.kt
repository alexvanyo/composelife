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

import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver

/**
 * A nestable representation of a string resource or a quantity string resource.
 */
actual sealed class ParameterizedString {

    internal abstract val args: List<Any>

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
        is ParameterizedString.BasicString -> {
            listOf(parameterizedString.value)
        }
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

private fun restore(list: List<Any>): ParameterizedString =
    ParameterizedString.BasicString(
        value = list[0] as String,
        args = list.drop(1).map { arg ->
            @Suppress("UNCHECKED_CAST")
            arg as List<Any>
            val type = arg[0] as Int
            when (type) {
                0 -> @Suppress("UNCHECKED_CAST") restore(arg[1] as List<Any>)
                1 -> arg[1]
                else -> error("Unexpected type $type")
            }
        }
    )

/**
 * Creates a representation of a plain-text string.
 */
actual fun ParameterizedString(
    value: String,
    vararg args: Any,
): ParameterizedString = ParameterizedString.BasicString(
    value = value,
    args = args.toList(),
)

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

/**
 * A nestable representation of a string resource or a quantity string resource.
 */
actual sealed class ParameterizedString {

    internal abstract val args: List<Any>

    internal data class BasicString(
        val value: String,
        override val args: List<Any>,
    ) : ParameterizedString()
}

/**
 * Creates a representation of a string resource [stringRes] with optional [args].
 */
fun ParameterizedString(
    value: String,
    vararg args: Any,
): ParameterizedString = ParameterizedString.BasicString(
    value = value,
    args = args.toList(),
)

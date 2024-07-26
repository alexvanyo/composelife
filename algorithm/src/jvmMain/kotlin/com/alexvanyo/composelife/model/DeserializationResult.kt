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

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

/**
 * A result of deserializing into a [CellState].
 */
sealed interface DeserializationResult {

    /**
     * A list of warnings encountered while deserializing.
     */
    val warnings: List<ParameterizedString>

    /**
     * A successful deserialization with [format] into the given [cellState].
     */
    data class Successful(
        override val warnings: List<ParameterizedString>,
        val cellState: CellState,
        val format: CellStateFormat.FixedFormat,
    ) : DeserializationResult

    /**
     * An unsuccessful deserialization, with the given [errors].
     */
    data class Unsuccessful(
        override val warnings: List<ParameterizedString>,
        val errors: List<ParameterizedString>,
    ) : DeserializationResult
}

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

import androidx.compose.runtime.saveable.Saver
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.serialization.saver
import kotlinx.serialization.Serializable
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * A result of deserializing into a [CellState].
 */
@Serializable
sealed interface DeserializationResult {

    /**
     * A list of warnings encountered while deserializing.
     */
    val warnings: List<ParameterizedString>

    /**
     * A successful deserialization with [format] into the given [cellState].
     */
    @Serializable
    data class Successful(
        override val warnings: List<ParameterizedString>,
        val cellState: CellState,
        val format: CellStateFormat.FixedFormat,
    ) : DeserializationResult

    /**
     * An unsuccessful deserialization, with the given [errors].
     */
    @Serializable
    data class Unsuccessful(
        override val warnings: List<ParameterizedString>,
        val errors: List<ParameterizedString>,
    ) : DeserializationResult

    companion object {
        val Saver: Saver<DeserializationResult, SavedState> = serializer().saver()
    }
}

@OptIn(ExperimentalContracts::class)
fun DeserializationResult.isSuccessful(): Boolean {
    contract {
        returns(true) implies (this@isSuccessful is DeserializationResult.Successful)
        returns(false) implies (this@isSuccessful is DeserializationResult.Unsuccessful)
    }
    return when (this) {
        is DeserializationResult.Successful -> true
        is DeserializationResult.Unsuccessful -> false
    }
}

fun Iterable<DeserializationResult>.reduceToSuccessful(): DeserializationResult =
    reduce { a, b ->
        when (a) {
            is DeserializationResult.Unsuccessful -> b
            is DeserializationResult.Successful -> {
                when (b) {
                    is DeserializationResult.Successful -> if (a.warnings.isEmpty()) {
                        a
                    } else {
                        b
                    }

                    is DeserializationResult.Unsuccessful -> a
                }
            }
        }
    }

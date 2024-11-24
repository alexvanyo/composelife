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
import androidx.compose.runtime.saveable.listSaver
import androidx.savedstate.SavedState
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.Saver
import com.alexvanyo.composelife.serialization.saver
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

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

    companion object {
        val Saver: Saver<DeserializationResult, Any> =
            listSaver(
                save = {
                    when (it) {
                        is Successful -> {
                            listOf(
                                0,
                                with(CellStateFormat.FixedFormat.serializer().saver) {
                                    save(it.format)
                                },
                                with(CellState.serializer().saver) {
                                    save(it.cellState)
                                },
                                it.warnings.map { warning ->
                                    with(ParameterizedString.Saver) {
                                        save(warning)
                                    }
                                },
                            )
                        }
                        is Unsuccessful -> {
                            listOf(
                                1,
                                it.warnings.map { warning ->
                                    with(ParameterizedString.Saver) {
                                        save(warning)
                                    }
                                },
                                it.errors.map { error ->
                                    with(ParameterizedString.Saver) {
                                        save(error)
                                    }
                                },
                            )
                        }
                    }
                },
                restore = {
                    val type = it[0] as Int
                    when (type) {
                        0 -> {
                            Successful(
                                format =
                                CellStateFormat.FixedFormat.serializer().saver.restore(it[1] as SavedState)!!,
                                cellState =
                                CellState.serializer().saver.restore(it[2] as SavedState)!!,
                                warnings = (it[3] as List<Any>).map {
                                    ParameterizedString.Saver.restore(it)!!
                                },
                            )
                        }
                        1 -> {
                            Unsuccessful(
                                warnings = (it[1] as List<Any>).map {
                                    ParameterizedString.Saver.restore(it)!!
                                },
                                errors = (it[2] as List<Any>).map {
                                    ParameterizedString.Saver.restore(it)!!
                                },
                            )
                        }
                        else -> error("Unexpected type $type")
                    }
                },
            )
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

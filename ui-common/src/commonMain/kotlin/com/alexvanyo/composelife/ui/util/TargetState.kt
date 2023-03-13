/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.util

import androidx.annotation.FloatRange
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * A state describing a target value, with the ability to declaratively specify to be partway between two states.
 *
 * Although a [TargetState] may result in showing multiple states [T] for an indeterminate amount of time, there is
 * still a single current semantic state given by [current].
 */
sealed interface TargetState<T> {

    /**
     * The "current" value of the [TargetState]. This represents the current semantic value for the target state,
     * which may be different from the state currently visible (due to ongoing animations).
     */
    val current: T

    /**
     * The target state is the single [current] value.
     */
    data class Single<T>(
        override val current: T
    ) : TargetState<T>

    /**
     * The target state is partway between [current] and [provisional], with the fraction given by [progress] from
     * [current] to [provisional].
     *
     * [current] should be different from [provisional], since otherwise [Single] should be used instead (with the
     * single value).
     */
    data class InProgress<T>(
        override val current: T,

        /**
         * The "provisional" state of an in-progress animation. This is a state [T] that could become the [current]
         * state, but is not at the moment the semantically current state.
         */
        val provisional: T,

        /**
         * The progress from [current] to [provisional].
         */
        @FloatRange(from = 0.0, to = 1.0)
        val progress: Float,
    ) : TargetState<T> {
        init {
            require(current != provisional) {
                "current is the same as provisional, should be using TargetState.Single instead"
            }
        }
    }
}

/**
 * Returns `true` if this [TargetState] is in progress, otherwise `false`.
 */
@OptIn(ExperimentalContracts::class)
fun <T> TargetState<T>.isInProgress(): Boolean {
    contract {
        returns(false) implies (this@isInProgress is TargetState.Single<T>)
        returns(true) implies (this@isInProgress is TargetState.InProgress<T>)
    }
    return when (this) {
        is TargetState.Single -> false
        is TargetState.InProgress -> true
    }
}

/**
 * Returns the normalized progress from `false` to `true` for a [TargetState] of a [Boolean].
 *
 * [TargetState.Single] of `true` will map to `1f,` and [TargetState.Single] of `false` will map to `0f`.
 */
val TargetState<Boolean>.progressToTrue: Float get() =
    when (this) {
        is TargetState.InProgress -> if (provisional) progress else 1f - progress
        is TargetState.Single -> if (current) 1f else 0f
    }

/**
 * Negates the [TargetState]. This negation is transitive for [TargetState.current]: that is,
 * `targetState.not().current` will be equal to `targetState.current.not()`.
 */
operator fun TargetState<Boolean>.not(): TargetState<Boolean> = map(Boolean::not)

/**
 * Applies an and operation on a [TargetState] with a non-[TargetState] [Boolean] value.
 *
 * Because [value] is not animating, this will collapse a [TargetState.InProgress] value to a [TargetState.Single] of
 * `false` if [value] is `false`.
 */
infix fun TargetState<Boolean>.and(value: Boolean): TargetState<Boolean> =
    if (value) {
        this
    } else {
        TargetState.Single(false)
    }

/**
 * Applies an or operation on a [TargetState] with a non-[TargetState] [Boolean] value.
 *
 * Because [value] is not animating, this will collapse a [TargetState.InProgress] value to a [TargetState.Single] of
 * `true` if [value] is `true`.
 */
infix fun TargetState<Boolean>.or(value: Boolean): TargetState<Boolean> =
    if (value) {
        TargetState.Single(true)
    } else {
        this
    }

/**
 * Maps this [TargetState] of type [T] to the [TargetState] of type [R] using [lambda].
 */
fun <T, R> TargetState<T>.map(lambda: (T) -> R): TargetState<R> =
    when (this) {
        is TargetState.Single -> TargetState.Single(current.let(lambda))
        is TargetState.InProgress -> TargetState.InProgress(
            current = current.let(lambda),
            provisional = provisional.let(lambda),
            progress = progress,
        )
    }

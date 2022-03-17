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

package com.alexvanyo.composelife.resourcestate

import androidx.compose.runtime.Composable
import androidx.compose.runtime.State
import androidx.compose.runtime.collectAsState
import com.alexvanyo.composelife.resourcestate.ResourceState.Failure
import com.alexvanyo.composelife.resourcestate.ResourceState.Loading
import com.alexvanyo.composelife.resourcestate.ResourceState.Success
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.catch
import kotlinx.coroutines.flow.first
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.transform
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

/**
 * A simple sealed class indicating a state of a resource that has to be loaded, with the opportunity to be a success
 * or a failure.
 */
sealed interface ResourceState<out T : Any> {

    /**
     * The resource is loading.
     */
    object Loading : ResourceState<Nothing>

    /**
     * The resource is successfully loaded, with the given [value].
     */
    data class Success<T : Any>(
        val value: T
    ) : ResourceState<T>

    /**
     * Loading the resource failed with the given [throwable].
     */
    data class Failure<T : Any>(
        val throwable: Throwable
    ) : ResourceState<T>
}

/**
 * Returns `true` if and only if this is a success.
 */
@OptIn(ExperimentalContracts::class)
fun <T : Any> ResourceState<T>.isSuccess(): Boolean {
    contract { returns(true) implies (this@isSuccess is Success) }

    return when (this) {
        Loading -> false
        is Success -> true
        is Failure -> false
    }
}

/**
 * Returns a filtered [Flow] of only the successful [ResourceState]s.
 */
fun <T : Any> Flow<ResourceState<T>>.successes(): Flow<Success<T>> =
    transform { resourceState ->
        if (resourceState.isSuccess()) {
            emit(resourceState)
        }
    }

/**
 * Returns the first successful value from the given [Flow].
 */
suspend fun <T : Any> Flow<ResourceState<T>>.firstSuccess(): Success<T> =
    successes().first()

/**
 * Maps the given [ResourceState] into another, with a [transform] upon the underlying values.
 *
 * [Loading] and [Failure]s are simply returned with the proper type.
 */
inline fun <T : Any, R : Any> ResourceState<T>.map(transform: (T) -> R): ResourceState<R> = when (this) {
    Loading -> Loading
    is Success -> Success(transform(value))
    is Failure -> Failure(throwable)
}

/**
 * Flat maps the given [ResourceState] into another, with a [transform] that produces another [ResourceState].
 *
 * [Loading] and [Failure]s are simply returned with the proper type.
 */
inline fun <T : Any, R : Any> ResourceState<T>.flatMap(
    transform: (T) -> ResourceState<R>
): ResourceState<R> = when (this) {
    Loading -> Loading
    is Success -> transform(value)
    is Failure -> Failure(throwable)
}

/**
 * Combines two [ResourceState]s into a single one.
 *
 * If either is a failure, then the resulting [ResourceState] will also be a failure.
 *
 * Otherwise, if either is loading, then the resulting [ResourceState] will be loading.
 *
 * Otherwise, both are successful, and the successful values will be sent to [transform].
 */
inline fun <T1 : Any, T2 : Any, R : Any> combine(
    resourceState1: ResourceState<T1>,
    resourceState2: ResourceState<T2>,
    transform: (a: T1, b: T2) -> R
): ResourceState<R> = combine(
    resourceState1,
    resourceState2,
) { list: List<Any> ->
    @Suppress("UNCHECKED_CAST")
    transform(list[0] as T1, list[1] as T2)
}

/**
 * Combines three [ResourceState]s into a single one.
 *
 * If any is a failure, then the resulting [ResourceState] will also be a failure.
 *
 * Otherwise, if any are loading, then the resulting [ResourceState] will be loading.
 *
 * Otherwise, all are successful, and the successful values will be sent to [transform].
 */
inline fun <T1 : Any, T2 : Any, T3 : Any, R : Any> combine(
    resourceState1: ResourceState<T1>,
    resourceState2: ResourceState<T2>,
    resourceState3: ResourceState<T3>,
    transform: (a: T1, b: T2, c: T3) -> R
): ResourceState<R> = combine(
    resourceState1,
    resourceState2,
    resourceState3,
) { list: List<Any> ->
    @Suppress("UNCHECKED_CAST")
    transform(list[0] as T1, list[1] as T2, list[2] as T3)
}

/**
 * Combines an arbitrary number of [ResourceState]s into a single one.
 *
 * If any is a failure, then the resulting [ResourceState] will also be a failure.
 *
 * Otherwise, if any is loading, then the resulting [ResourceState] will be loading.
 *
 * Otherwise, all are successful, and the successful values will be sent to [transform].
 */
inline fun <R : Any> combine(
    vararg resourceStates: ResourceState<*>,
    transform: (args: List<Any>) -> R
): ResourceState<R> {
    val loading = resourceStates.filterIsInstance<Loading>()
    val failures = resourceStates.filterIsInstance<Failure<*>>()
    val successes = resourceStates.filterIsInstance<Success<*>>()
    return when {
        failures.isNotEmpty() -> {
            Failure(
                if (failures.size == 1) {
                    failures.first().throwable
                } else {
                    CompositeException(failures.map { it.throwable })
                }
            )
        }
        loading.isNotEmpty() -> Loading
        else -> {
            check(resourceStates.size == successes.size)
            Success(
                transform(successes.map { it.value })
            )
        }
    }
}

/**
 * Converts the given [Flow] into a [ResourceState], mapping successes to [Success] and catching and
 * re-emitting exceptions as [Failure].
 */
fun <T : Any> Flow<T>.asResourceState(): Flow<ResourceState<T>> =
    map<T, ResourceState<T>>(::Success).catch { emit(Failure(it)) }

/**
 * Collects the given [Flow] of [ResourceState] as a [State], with an initial value of [Loading].
 */
@Composable
fun <T : Any> Flow<ResourceState<T>>.collectAsState(): State<ResourceState<T>> = collectAsState(initial = Loading)

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

sealed interface ResourceState<out T : Any> {
    object Loading : ResourceState<Nothing>

    data class Success<T : Any>(
        val value: T
    ) : ResourceState<T>

    data class Failure<T : Any>(
        val throwable: Throwable
    ) : ResourceState<T>
}

@OptIn(ExperimentalContracts::class)
fun <T : Any> ResourceState<T>.isSuccess(): Boolean {
    contract { returns(true) implies (this@isSuccess is Success) }

    return when (this) {
        Loading -> false
        is Success -> true
        is Failure -> false
    }
}

fun <T : Any> Flow<ResourceState<T>>.successes(): Flow<Success<T>> =
    transform { resourceState ->
        if (resourceState.isSuccess()) {
            emit(resourceState)
        }
    }

suspend fun <T : Any> Flow<ResourceState<T>>.firstSuccess(): Success<T> =
    successes().first()

inline fun <T : Any, R : Any> ResourceState<T>.map(transform: (T) -> R): ResourceState<R> = when (this) {
    Loading -> Loading
    is Success -> Success(transform(value))
    is Failure -> Failure(throwable)
}

inline fun <T : Any, R : Any> ResourceState<T>.flatMap(
    transform: (T) -> ResourceState<R>
): ResourceState<R> = when (this) {
    Loading -> Loading
    is Success -> transform(value)
    is Failure -> Failure(throwable)
}

inline fun <T1 : Any, T2 : Any, R : Any> combine(
    resourceState1: ResourceState<T1>,
    resourceState2: ResourceState<T2>,
    transform: (a: T1, b: T2) -> R
): ResourceState<R> = when (resourceState1) {
    Loading -> when (resourceState2) {
        Loading,
        is Success -> Loading
        is Failure -> Failure(resourceState2.throwable)
    }
    is Success -> when (resourceState2) {
        Loading -> Loading
        is Success -> Success(transform(resourceState1.value, resourceState2.value))
        is Failure -> Failure(resourceState2.throwable)
    }
    is Failure -> when (resourceState2) {
        Loading,
        is Success -> Failure(resourceState1.throwable)
        is Failure -> Failure(resourceState1.throwable.apply { addSuppressed(resourceState2.throwable) })
    }
}

fun <T : Any> Flow<T>.asResourceState(): Flow<ResourceState<T>> =
    map<T, ResourceState<T>>(::Success).catch { emit(Failure(it)) }

@Composable
fun <T : Any> Flow<ResourceState<T>>.collectAsState(): State<ResourceState<T>> = collectAsState(initial = Loading)

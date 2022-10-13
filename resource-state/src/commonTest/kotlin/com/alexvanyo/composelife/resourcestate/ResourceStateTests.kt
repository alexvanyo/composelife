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

import app.cash.turbine.test
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

@Suppress("LargeClass")
@OptIn(ExperimentalCoroutinesApi::class)
class ResourceStateTests {

    @Test
    fun success_resource_state_is_correct() = runTest {
        flow {
            emit("a")
        }
            .asResourceState()
            .test {
                assertEquals(ResourceState.Success("a"), awaitItem())
                awaitComplete()
            }
    }

    @Test
    fun multiple_success_resource_state_is_correct() = runTest {
        flow {
            emit("a")
            emit("b")
            emit("c")
        }
            .asResourceState()
            .test {
                assertEquals(ResourceState.Success("a"), awaitItem())
                assertEquals(ResourceState.Success("b"), awaitItem())
                assertEquals(ResourceState.Success("c"), awaitItem())
                awaitComplete()
            }
    }

    @Test
    fun success_resource_state_with_exception_is_correct() = runTest {
        val exception = Exception()

        flow {
            emit("a")
            emit("b")
            emit("c")
            throw exception
        }
            .asResourceState()
            .test {
                assertEquals(ResourceState.Success("a"), awaitItem())
                assertEquals(ResourceState.Success("b"), awaitItem())
                assertEquals(ResourceState.Success("c"), awaitItem())
                assertEquals(ResourceState.Failure(exception), awaitItem())
                awaitComplete()
            }
    }

    @Test
    fun filtered_successes_flow_is_correct() = runTest {
        flow {
            emit(ResourceState.Loading)
            emit(ResourceState.Success("a"))
            emit(ResourceState.Loading)
            emit(ResourceState.Success("b"))
            emit(ResourceState.Loading)
            emit(ResourceState.Failure(Exception()))
            emit(ResourceState.Success("c"))
        }.successes().test {
            assertEquals(ResourceState.Success("a"), awaitItem())
            assertEquals(ResourceState.Success("b"), awaitItem())
            assertEquals(ResourceState.Success("c"), awaitItem())
            awaitComplete()
        }
    }

    @Test
    fun first_successes_is_correct() = runTest {
        assertEquals(
            ResourceState.Success("a"),
            flow {
                emit(ResourceState.Loading)
                emit(ResourceState.Success("a"))
                emit(ResourceState.Loading)
                emit(ResourceState.Success("b"))
                emit(ResourceState.Loading)
                emit(ResourceState.Failure(Exception()))
                emit(ResourceState.Success("c"))
            }.firstSuccess(),
        )
    }

    @Test
    fun loading_is_not_a_success() {
        assertFalse(ResourceState.Loading.isSuccess())
    }

    @Test
    fun failure_is_not_a_success() {
        assertFalse(ResourceState.Failure<String>(Exception()).isSuccess())
    }

    @Test
    fun success_is_a_success() {
        val resourceState: ResourceState<String> = ResourceState.Success("a")
        assertTrue(resourceState.isSuccess())
        // Check that type is inferred
        assertEquals("a", resourceState.value)
    }

    @Test
    fun map_loading_results_in_loading() {
        val resourceState: ResourceState<Char> = ResourceState.Loading
        assertEquals(ResourceState.Loading, resourceState.map { it.code })
    }

    @Test
    fun map_failure_results_in_failure() {
        val exception = Exception()
        val resourceState: ResourceState<Char> = ResourceState.Failure(exception)
        assertEquals(ResourceState.Failure(exception), resourceState.map { it.code })
    }

    @Test
    fun map_success_results_in_success() {
        val resourceState: ResourceState<Char> = ResourceState.Success('a')
        assertEquals(ResourceState.Success(97), resourceState.map { it.code })
    }

    private suspend fun getResourceState(): ResourceState<Int> {
        delay(1000)
        return ResourceState.Success(42)
    }

    @Test
    fun flat_map_loading_results_in_loading() = runTest {
        val resourceState: ResourceState<Char> = ResourceState.Loading
        assertEquals(
            ResourceState.Loading,
            resourceState.flatMap { getResourceState() },
        )
    }

    @Test
    fun flat_map_failure_results_in_failure() = runTest {
        val exception = Exception()
        val resourceState: ResourceState<Char> = ResourceState.Failure(exception)
        assertEquals(
            ResourceState.Failure(exception),
            resourceState.flatMap { getResourceState() },
        )
    }

    @Test
    fun flat_map_success_results_in_success() = runTest {
        val resourceState: ResourceState<Char> = ResourceState.Success('a')
        assertEquals(
            ResourceState.Success(42),
            resourceState.flatMap { getResourceState() },
        )
    }

    @Test
    fun loading_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Loading,
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun loading_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Loading,
                ResourceState.Failure(exception),
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun loading_and_success_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Success("b"),
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun failure_and_loading_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Loading,
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun failure_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
        ) { a: String, b: String ->
            a + b
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun failure_and_success_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Success("b"),
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun success_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Success("a"),
                ResourceState.Loading,
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun success_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Success("a"),
                ResourceState.Failure(exception),
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun success_and_success_results_in_success() = runTest {
        assertEquals(
            ResourceState.Success("ab"),
            combine(
                ResourceState.Success("a"),
                ResourceState.Success("b"),
            ) { a: String, b: String ->
                a + b
            },
        )
    }

    @Test
    fun loading_loading_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Loading,
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_loading_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Loading,
                ResourceState.Loading,
                ResourceState.Failure(exception),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_loading_and_success_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Loading,
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_failure_and_loading_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Loading,
                ResourceState.Failure(exception),
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_failure_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Loading,
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun loading_failure_and_success_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Loading,
                ResourceState.Failure(exception),
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_success_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Success("b"),
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_success_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Loading,
                ResourceState.Success("b"),
                ResourceState.Failure(exception),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun loading_success_and_success_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Loading,
                ResourceState.Success("b"),
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun failure_loading_and_loading_results_in_failure() = runTest {
        val exception = Exception()

        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Loading,
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun failure_loading_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Loading,
            ResourceState.Failure(exception2),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun failure_loading_and_success_results_in_failure() = runTest {
        val exception = Exception()

        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Loading,
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun failure_failure_and_loading_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
            ResourceState.Loading,
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun failure_failure_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val exception3 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
            ResourceState.Failure(exception3),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("3 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2, exception3), throwable.exceptions)
    }

    @Test
    fun failure_failure_and_success_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
            ResourceState.Success("c"),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun failure_success_and_loading_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Success("b"),
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun failure_success_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Failure(exception1),
            ResourceState.Success("b"),
            ResourceState.Failure(exception2),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun failure_success_and_success_results_in_success() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Failure(exception),
                ResourceState.Success("b"),
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_loading_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Success("a"),
                ResourceState.Loading,
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_loading_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Success("a"),
                ResourceState.Loading,
                ResourceState.Failure(exception),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_loading_and_success_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Success("a"),
                ResourceState.Loading,
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_failure_and_loading_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Success("a"),
                ResourceState.Failure(exception),
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_failure_and_failure_results_in_failure() = runTest {
        val exception1 = Exception()
        val exception2 = Exception()
        val result = combine(
            ResourceState.Success("a"),
            ResourceState.Failure(exception1),
            ResourceState.Failure(exception2),
        ) { a: String, b: String, c: String ->
            a + b + c
        }

        assertIs<ResourceState.Failure<String>>(result)
        val throwable = result.throwable

        assertIs<CompositeException>(throwable)
        assertEquals("2 exceptions occurred.", throwable.message)
        assertEquals(exception1, throwable.cause)
        assertEquals(listOf(exception1, exception2), throwable.exceptions)
    }

    @Test
    fun success_failure_and_success_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Success("a"),
                ResourceState.Failure(exception),
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_success_and_loading_results_in_loading() = runTest {
        assertEquals(
            ResourceState.Loading,
            combine(
                ResourceState.Success("a"),
                ResourceState.Success("b"),
                ResourceState.Loading,
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_success_and_failure_results_in_failure() = runTest {
        val exception = Exception()
        assertEquals(
            ResourceState.Failure(exception),
            combine(
                ResourceState.Success("a"),
                ResourceState.Success("b"),
                ResourceState.Failure(exception),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }

    @Test
    fun success_success_and_success_results_in_success() = runTest {
        assertEquals(
            ResourceState.Success("abc"),
            combine(
                ResourceState.Success("a"),
                ResourceState.Success("b"),
                ResourceState.Success("c"),
            ) { a: String, b: String, c: String ->
                a + b + c
            },
        )
    }
}

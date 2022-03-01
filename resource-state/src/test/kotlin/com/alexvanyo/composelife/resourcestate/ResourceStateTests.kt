package com.alexvanyo.composelife.resourcestate

import app.cash.turbine.test
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.test.runTest
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

@OptIn(ExperimentalCoroutinesApi::class)
class ResourceStateTests {

    @Nested
    inner class AsResourceStateTests {

        @Test
        fun `success resource state is correct`() = runTest {
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
        fun `multiple success resource state is correct`() = runTest {
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
        fun `success resource state with exception is correct`() = runTest {
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
    }

    @Nested
    inner class SuccessesTests {

        @Test
        fun `filtered successes flow is correct`() = runTest {
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
    }

    @Nested
    inner class FirstSuccessTests {

        @Test
        fun `first successes is correct`() = runTest {
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
                }.firstSuccess()
            )
        }
    }

    @Nested
    inner class IsSuccessTests {

        @Test
        fun `loading is not a success`() {
            assertFalse(ResourceState.Loading.isSuccess())
        }

        @Test
        fun `failure is not a success`() {
            assertFalse(ResourceState.Failure<String>(Exception()).isSuccess())
        }

        @Test
        fun `success is a success`() {
            val resourceState: ResourceState<String> = ResourceState.Success("a")
            assertTrue(resourceState.isSuccess())
            // Check that type is inferred
            assertEquals("a", resourceState.value)
        }
    }

    @Nested
    inner class MapTests {

        @Test
        fun `map loading results in loading`() {
            val resourceState: ResourceState<Char> = ResourceState.Loading
            assertEquals(ResourceState.Loading, resourceState.map { it.code })
        }

        @Test
        fun `map failure results in failure`() {
            val exception = Exception()
            val resourceState: ResourceState<Char> = ResourceState.Failure(exception)
            assertEquals(ResourceState.Failure(exception), resourceState.map { it.code })
        }

        @Test
        fun `map success results in success`() {
            val resourceState: ResourceState<Char> = ResourceState.Success('a')
            assertEquals(ResourceState.Success(97), resourceState.map { it.code })
        }
    }

    @Nested
    inner class FlatMapTests {

        private suspend fun getResourceState(): ResourceState<Int> {
            delay(1000)
            return ResourceState.Success(42)
        }

        @Test
        fun `map loading results in loading`() = runTest {
            val resourceState: ResourceState<Char> = ResourceState.Loading
            assertEquals(
                ResourceState.Loading,
                resourceState.flatMap { getResourceState() }
            )
        }

        @Test
        fun `map failure results in failure`() = runTest {
            val exception = Exception()
            val resourceState: ResourceState<Char> = ResourceState.Failure(exception)
            assertEquals(
                ResourceState.Failure(exception),
                resourceState.flatMap { getResourceState() }
            )
        }

        @Test
        fun `map success results in success`() = runTest {
            val resourceState: ResourceState<Char> = ResourceState.Success('a')
            assertEquals(
                ResourceState.Success(42),
                resourceState.flatMap { getResourceState() }
            )
        }
    }

    @Nested
    inner class CombineTests {

        @Test
        fun `loading and loading results in loading`() = runTest {
            assertEquals(
                ResourceState.Loading,
                combine(
                    ResourceState.Loading,
                    ResourceState.Loading
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `loading and failure results in failure`() = runTest {
            val exception = Exception()
            assertEquals(
                ResourceState.Failure(exception),
                combine(
                    ResourceState.Loading,
                    ResourceState.Failure(exception)
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `loading and success results in loading`() = runTest {
            assertEquals(
                ResourceState.Loading,
                combine(
                    ResourceState.Loading,
                    ResourceState.Success("b")
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `failure and loading results in failure`() = runTest {
            val exception = Exception()
            assertEquals(
                ResourceState.Failure(exception),
                combine(
                    ResourceState.Failure(exception),
                    ResourceState.Loading
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `failure and failure results in failure`() = runTest {
            val exception1 = Exception()
            val exception2 = Exception()
            val result = combine(
                ResourceState.Failure(exception1),
                ResourceState.Failure(exception2)
            ) { a: String, b: String ->
                a + b
            }

            assertIs<ResourceState.Failure<String>>(result)

            assertEquals(exception1, result.throwable)
            assertEquals(listOf(exception2), result.throwable.suppressedExceptions)
        }

        @Test
        fun `failure and success results in failure`() = runTest {
            val exception = Exception()
            assertEquals(
                ResourceState.Failure(exception),
                combine(
                    ResourceState.Failure(exception),
                    ResourceState.Success("b")
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `success and loading results in failure`() = runTest {
            assertEquals(
                ResourceState.Loading,
                combine(
                    ResourceState.Success("a"),
                    ResourceState.Loading
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `success and failure results in failure`() = runTest {
            val exception = Exception()
            assertEquals(
                ResourceState.Failure(exception),
                combine(
                    ResourceState.Success("a"),
                    ResourceState.Failure(exception)
                ) { a: String, b: String ->
                    a + b
                }
            )
        }

        @Test
        fun `success and success results in success`() = runTest {
            assertEquals(
                ResourceState.Success("ab"),
                combine(
                    ResourceState.Success("a"),
                    ResourceState.Success("b")
                ) { a: String, b: String ->
                    a + b
                }
            )
        }
    }
}

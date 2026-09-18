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

import androidx.appstate.transform.transform
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@OptIn(ExperimentalCoroutinesApi::class)
class ResourceStateComposableTests {

    @Suppress("ThrowingExceptionsWithoutMessageOrCause")
    @Test
    fun collect_as_state_is_correct() = runTest {
        val channel = Channel<String>()

        val state = transform<ResourceState<String>>(
            initialValue = ResourceState.Loading,
            scope = backgroundScope,
            dispatcher = StandardTestDispatcher(testScheduler),
        ) {
            val resourceState by remember {
                channel.receiveAsFlow().asResourceState()
            }.collectAsState()

            resourceState
        }

        assertEquals(ResourceState.Loading, state.value)

        channel.send("a")
        runCurrent()

        assertEquals(ResourceState.Success("a"), state.value)

        val exception = TestException()
        channel.close(exception)
        runCurrent()

        state.value.let { result ->
            val _ = assertIs<ResourceState.Failure<String>>(result)
            val _ = assertIs<TestException>(result.throwable)
        }
    }
}

private class TestException : Exception()

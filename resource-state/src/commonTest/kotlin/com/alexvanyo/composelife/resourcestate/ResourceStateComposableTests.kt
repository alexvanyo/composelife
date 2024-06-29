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

import androidx.compose.runtime.BroadcastFrameClock
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import app.cash.molecule.RecompositionMode
import app.cash.molecule.moleculeFlow
import app.cash.turbine.test
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

class ResourceStateComposableTests {

    private val broadcastFrameClock = BroadcastFrameClock()

    @Suppress("ThrowingExceptionsWithoutMessageOrCause")
    @Test
    fun collect_as_state_is_correct() = runTest(broadcastFrameClock) {
        val channel = Channel<String>()

        moleculeFlow(RecompositionMode.ContextClock) {
            val state by remember {
                channel.receiveAsFlow().asResourceState()
            }.collectAsState()

            state
        }
            .test {
                assertEquals(ResourceState.Loading, awaitItem())

                channel.send("a")
                broadcastFrameClock.sendFrame(1)

                assertEquals(ResourceState.Success("a"), awaitItem())

                val exception = TestException()
                channel.close(exception)
                broadcastFrameClock.sendFrame(2)

                awaitItem().let { state ->
                    assertIs<ResourceState.Failure<String>>(state)
                    assertIs<TestException>(state.throwable)
                }
            }
    }
}

private class TestException : Exception()

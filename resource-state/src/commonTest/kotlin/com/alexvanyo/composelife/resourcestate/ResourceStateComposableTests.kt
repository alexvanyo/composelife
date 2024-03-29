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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@Suppress("UnnecessaryAbstractClass")
@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ResourceStateComposableTests {

    @Suppress("ThrowingExceptionsWithoutMessageOrCause")
    @Test
    fun collect_as_state_is_correct() = runComposeUiTest {
        runTest {
            var currentState: ResourceState<String>? = null

            val channel = Channel<String>()

            setContent {
                val state by remember {
                    channel.receiveAsFlow().asResourceState()
                }.collectAsState()

                currentState = state
            }

            waitForIdle()

            assertEquals(ResourceState.Loading, currentState)

            channel.send("a")
            waitForIdle()

            assertEquals(ResourceState.Success("a"), currentState)

            val exception = TestException()
            channel.close(exception)

            waitForIdle()

            currentState.let { state ->
                assertIs<ResourceState.Failure<String>>(state)
                assertIs<TestException>(state.throwable)
            }
        }
    }
}

private class TestException : Exception()

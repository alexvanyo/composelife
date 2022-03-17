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
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class ResourceStateComposableTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Suppress("ThrowingExceptionsWithoutMessageOrCause")
    @Test
    fun collect_as_state_is_correct() = runTest {
        var currentState: ResourceState<String>? = null

        val channel = Channel<String>()

        composeTestRule.setContent {
            val state by remember {
                channel.receiveAsFlow().asResourceState()
            }.collectAsState()

            currentState = state
        }

        composeTestRule.waitForIdle()

        assertEquals(ResourceState.Loading, currentState)

        channel.send("a")
        composeTestRule.waitForIdle()

        assertEquals(ResourceState.Success("a"), currentState)

        val exception = Exception()
        channel.close(exception)

        composeTestRule.waitForIdle()

        assertEquals(ResourceState.Failure(exception), currentState)
    }
}

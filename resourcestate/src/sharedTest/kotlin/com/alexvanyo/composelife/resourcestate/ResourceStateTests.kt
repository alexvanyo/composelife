package com.alexvanyo.composelife.resourcestate

import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import app.cash.turbine.test
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class ResourceStateTests {

    @get:Rule
    val composeTestRule = createComposeRule()

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
    fun collect_as_state_is_correct() = runTest {
        var currentState: ResourceState<String>? = null

        val channel = Channel<String>()

        composeTestRule.setContent {
            val state by remember {
                channel.receiveAsFlow().asResourceState()
            }.collectAsState()

            currentState = state
        }

        composeTestRule.awaitIdle()

        assertEquals(ResourceState.Loading, currentState)

        channel.send("a")
        composeTestRule.awaitIdle()

        assertEquals(ResourceState.Success("a"), currentState)

        val exception = Exception()
        channel.close(exception)

        composeTestRule.awaitIdle()

        assertEquals(ResourceState.Failure(exception), currentState)
    }
}

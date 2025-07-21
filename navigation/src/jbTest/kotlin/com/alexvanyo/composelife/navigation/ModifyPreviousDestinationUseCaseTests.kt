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

package com.alexvanyo.composelife.navigation

import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import org.junit.runner.RunWith
import kotlin.test.Test

private class TestPaneState(
    private val previous: TestPaneState?,
    initialCount: Int = 0,
) {
    var count by mutableStateOf(initialCount)
        private set

    val canIncrementPrevious: Boolean get() = previous != null

    fun increment() {
        count++
    }

    fun incrementPrevious() {
        check(canIncrementPrevious)
        @Suppress("UnsafeCallOnNullableType")
        previous!!.increment()
    }

    companion object : BackstackValueSaverFactory<TestPaneState> {
        override fun create(previous: BackstackEntry<TestPaneState>?): Saver<TestPaneState, Any> =
            Saver(
                save = { it.count },
                restore = {
                    TestPaneState(
                        previous = previous?.value,
                        initialCount = it as Int,
                    )
                },
            )
    }
}

@OptIn(ExperimentalAnimationApi::class, ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ModifyPreviousDestinationUseCaseTests {

    @Suppress("LongMethod")
    @Test
    fun can_increment_count_on_previous_pane() = runComposeUiTest {
        setContent {
            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        TestPaneState(
                            previous = null,
                        ),
                        previous = null,
                    ),
                ),
                backstackValueSaverFactory = TestPaneState,
            )

            NavigationHost(
                navigationState = navController,
            ) { entry ->
                Column {
                    BasicText("count: ${entry.value.count}")
                    BasicText(
                        "increment current",
                        Modifier.clickable {
                            entry.value.increment()
                        },
                    )
                    if (entry.value.canIncrementPrevious) {
                        BasicText(
                            "increment previous",
                            Modifier.clickable {
                                entry.value.incrementPrevious()
                            },
                        )
                    }
                    if (navController.canNavigateBack) {
                        BasicText(
                            "navigate back",
                            Modifier.clickable {
                                navController.withExpectedActor(entry.id) {
                                    popBackstack()
                                }
                            },
                        )
                    }
                    BasicText(
                        "navigate forward",
                        Modifier.clickable {
                            navController.withExpectedActor(entry.id) {
                                navigate(
                                    valueFactory = { previous ->
                                        TestPaneState(
                                            previous = previous.value,
                                        )
                                    },
                                )
                            }
                        },
                    )
                }
            }
        }

        onNodeWithText("count: 0").assertExists()
        onNodeWithText("navigate back").assertDoesNotExist()
        onNodeWithText("increment previous").assertDoesNotExist()

        onNodeWithText("increment current").performClick()

        onNodeWithText("count: 1").assertExists()

        onNodeWithText("navigate forward").performClick()

        onNodeWithText("count: 0").assertExists()
        onNodeWithText("navigate back").assertExists()

        onNodeWithText("increment previous").performClick()

        onNodeWithText("count: 0").assertExists()

        onNodeWithText("navigate back").performClick()

        onNodeWithText("count: 2").assertExists()
    }

    @Suppress("LongMethod")
    @Test
    fun can_increment_count_on_previous_pane_after_recreation() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        stateRestorationTester.setContent {
            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        TestPaneState(
                            previous = null,
                        ),
                        previous = null,
                    ),
                ),
                backstackValueSaverFactory = TestPaneState,
            )

            NavigationHost(
                navigationState = navController,
            ) { entry ->
                Column {
                    BasicText("count: ${entry.value.count}")
                    BasicText(
                        "increment current",
                        Modifier.clickable {
                            entry.value.increment()
                        },
                    )
                    if (entry.value.canIncrementPrevious) {
                        BasicText(
                            "increment previous",
                            Modifier.clickable {
                                entry.value.incrementPrevious()
                            },
                        )
                    }
                    if (navController.canNavigateBack) {
                        BasicText(
                            "navigate back",
                            Modifier.clickable {
                                navController.withExpectedActor(entry.id) {
                                    popBackstack()
                                }
                            },
                        )
                    }
                    BasicText(
                        "navigate forward",
                        Modifier.clickable {
                            navController.withExpectedActor(entry.id) {
                                navigate(
                                    valueFactory = { previous ->
                                        TestPaneState(
                                            previous = previous.value,
                                        )
                                    },
                                )
                            }
                        },
                    )
                }
            }
        }

        onNodeWithText("count: 0").assertExists()
        onNodeWithText("navigate back").assertDoesNotExist()
        onNodeWithText("increment previous").assertDoesNotExist()

        onNodeWithText("increment current").performClick()

        onNodeWithText("count: 1").assertExists()

        onNodeWithText("navigate forward").performClick()

        onNodeWithText("count: 0").assertExists()
        onNodeWithText("navigate back").assertExists()

        stateRestorationTester.emulateStateRestore()

        onNodeWithText("increment previous").performClick()

        onNodeWithText("count: 0").assertExists()

        onNodeWithText("navigate back").performClick()

        onNodeWithText("count: 2").assertExists()
    }
}

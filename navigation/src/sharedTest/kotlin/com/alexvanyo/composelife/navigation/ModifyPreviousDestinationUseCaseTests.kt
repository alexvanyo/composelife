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
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

private class TestScreenState(
    private val previous: TestScreenState?,
    initialCount: Int = 0
) {
    var count by mutableStateOf(initialCount)
        private set

    val canIncrementPrevious: Boolean get() = previous != null

    fun increment() {
        count++
    }

    fun incrementPrevious() {
        check(canIncrementPrevious)
        previous!!.increment()
    }

    companion object : BackstackValueSaverFactory<TestScreenState> {
        override fun create(previous: BackstackEntry<TestScreenState>?): Saver<TestScreenState, Any> =
            Saver(
                save = { it.count },
                restore = {
                    TestScreenState(
                        previous = previous?.value,
                        initialCount = it as Int
                    )
                }
            )
    }
}

@OptIn(ExperimentalAnimationApi::class)
@RunWith(AndroidJUnit4::class)
class ModifyPreviousDestinationUseCaseTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun can_increment_count_on_previous_screen() {
        composeTestRule.setContent {
            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        TestScreenState(
                            previous = null
                        ),
                        previous = null
                    )
                ),
                backstackValueSaverFactory = TestScreenState.Companion
            )

            NavigationHost(
                navigationState = navController
            ) { entry ->
                Column {
                    BasicText("count: ${entry.value.count}")
                    BasicText(
                        "increment current",
                        Modifier.clickable {
                            entry.value.increment()
                        }
                    )
                    if (entry.value.canIncrementPrevious) {
                        BasicText(
                            "increment previous",
                            Modifier.clickable {
                                entry.value.incrementPrevious()
                            }
                        )
                    }
                    if (navController.canNavigateBack) {
                        BasicText(
                            "navigate back",
                            Modifier.clickable {
                                navController.withExpectedActor(entry.id) {
                                    navController.popBackstack()
                                }
                            }
                        )
                    }
                    BasicText(
                        "navigate forward",
                        Modifier.clickable {
                            navController.withExpectedActor(entry.id) {
                                navController.navigate(
                                    valueFactory = {
                                        TestScreenState(
                                            previous = it.value,
                                        )
                                    }
                                )
                            }
                        }
                    )
                }
            }
        }

        composeTestRule.onNodeWithText("count: 0").assertExists()
        composeTestRule.onNodeWithText("navigate back").assertDoesNotExist()
        composeTestRule.onNodeWithText("increment previous").assertDoesNotExist()

        composeTestRule.onNodeWithText("increment current").performClick()

        composeTestRule.onNodeWithText("count: 1").assertExists()

        composeTestRule.onNodeWithText("navigate forward").performClick()

        composeTestRule.onNodeWithText("count: 0").assertExists()
        composeTestRule.onNodeWithText("navigate back").assertExists()

        composeTestRule.onNodeWithText("increment previous").performClick()

        composeTestRule.onNodeWithText("count: 0").assertExists()

        composeTestRule.onNodeWithText("navigate back").performClick()

        composeTestRule.onNodeWithText("count: 2").assertExists()
    }

    @Test
    fun can_increment_count_on_previous_screen_after_recreation() {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        stateRestorationTester.setContent {
            val navController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        TestScreenState(
                            previous = null
                        ),
                        previous = null
                    )
                ),
                backstackValueSaverFactory = TestScreenState.Companion
            )

            NavigationHost(
                navigationState = navController
            ) { entry ->
                Column {
                    BasicText("count: ${entry.value.count}")
                    BasicText(
                        "increment current",
                        Modifier.clickable {
                            entry.value.increment()
                        }
                    )
                    if (entry.value.canIncrementPrevious) {
                        BasicText(
                            "increment previous",
                            Modifier.clickable {
                                entry.value.incrementPrevious()
                            }
                        )
                    }
                    if (navController.canNavigateBack) {
                        BasicText(
                            "navigate back",
                            Modifier.clickable {
                                navController.withExpectedActor(entry.id) {
                                    navController.popBackstack()
                                }
                            }
                        )
                    }
                    BasicText(
                        "navigate forward",
                        Modifier.clickable {
                            navController.withExpectedActor(entry.id) {
                                navController.navigate(
                                    valueFactory = {
                                        TestScreenState(
                                            previous = it.value,
                                        )
                                    }
                                )
                            }
                        }
                    )
                }
            }
        }

        composeTestRule.onNodeWithText("count: 0").assertExists()
        composeTestRule.onNodeWithText("navigate back").assertDoesNotExist()
        composeTestRule.onNodeWithText("increment previous").assertDoesNotExist()

        composeTestRule.onNodeWithText("increment current").performClick()

        composeTestRule.onNodeWithText("count: 1").assertExists()

        composeTestRule.onNodeWithText("navigate forward").performClick()

        composeTestRule.onNodeWithText("count: 0").assertExists()
        composeTestRule.onNodeWithText("navigate back").assertExists()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        composeTestRule.onNodeWithText("increment previous").performClick()

        composeTestRule.onNodeWithText("count: 0").assertExists()

        composeTestRule.onNodeWithText("navigate back").performClick()

        composeTestRule.onNodeWithText("count: 2").assertExists()
    }
}

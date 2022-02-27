package com.alexvanyo.composelife.navigation

import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import java.util.UUID

enum class BackstackType {
    First,
    Second,
    Third
}

class MultipleMutableBackstackNavigationController(
    private val firstNavController: MutableBackstackNavigationController<String>,
    private val secondNavController: MutableBackstackNavigationController<String>,
    private val thirdNavController: MutableBackstackNavigationController<String>,
    initialSelectedBackstack: BackstackType = BackstackType.First
) : BackstackState<String> {

    var currentBackstack by mutableStateOf(initialSelectedBackstack)
        private set

    private val currentNavController: MutableBackstackNavigationController<String>
        get() = when (currentBackstack) {
            BackstackType.First -> firstNavController
            BackstackType.Second -> secondNavController
            BackstackType.Third -> thirdNavController
        }

    override val entryMap: BackstackMap<String>
        get() = firstNavController.entryMap + secondNavController.entryMap + thirdNavController.entryMap

    override var currentEntryId: UUID
        get() = currentNavController.currentEntryId
        set(value) {
            currentNavController.currentEntryId = value
        }

    val canNavigateBack: Boolean get() =
        currentEntry.previous != null ||
            when (currentBackstack) {
                BackstackType.First -> false
                BackstackType.Second, BackstackType.Third -> true
            }

    fun popBackstack() {
        if (currentEntry.previous != null) {
            currentNavController.popBackstack()
        } else {
            check(currentBackstack != BackstackType.First)
            currentBackstack = BackstackType.First
        }
    }

    fun onFirstClicked() {
        currentBackstack = BackstackType.First
    }

    fun onSecondClicked() {
        currentBackstack = BackstackType.Second
    }

    fun onThirdClicked() {
        currentBackstack = BackstackType.Third
    }

    companion object {

        fun saver(
            firstNavController: MutableBackstackNavigationController<String>,
            secondNavController: MutableBackstackNavigationController<String>,
            thirdNavController: MutableBackstackNavigationController<String>,
        ) : Saver<MultipleMutableBackstackNavigationController, Any> =
            Saver(
                save = { it.currentBackstack },
                restore = {
                    MultipleMutableBackstackNavigationController(
                        firstNavController = firstNavController,
                        secondNavController = secondNavController,
                        thirdNavController = thirdNavController,
                        initialSelectedBackstack = it as BackstackType
                    )
                }
            )
    }
}

@OptIn(ExperimentalAnimationApi::class)
@RunWith(AndroidJUnit4::class)
class MultipleBackstackUseCaseTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun can_increment_count_on_previous_screen() {
        composeTestRule.setContent {
            val firstNavController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        "first 1",
                        previous = null
                    )
                )
            )
            val secondNavController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        "second 1",
                        previous = null
                    )
                )
            )
            val thirdNavController = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        "third 1",
                        previous = null
                    )
                )
            )

            val navController = rememberSaveable(
                saver = MultipleMutableBackstackNavigationController.saver(
                    firstNavController,
                    secondNavController,
                    thirdNavController
                )
            ) {
                MultipleMutableBackstackNavigationController(
                    firstNavController = firstNavController,
                    secondNavController = secondNavController,
                    thirdNavController = thirdNavController
                )
            }

            NavigationHost(
                navigationState = navController
            ) { entry ->
                var count by rememberSaveable { mutableStateOf(0) }

                Column {
                    BasicText("value: ${entry.value}, count: $count")
                    BasicText(
                        "increment",
                        Modifier.clickable {
                            count++
                        }
                    )
                    if (navController.canNavigateBack) {
                        BasicText(
                            "navigate back",
                            Modifier.clickable {
                                navController.popBackstack()
                            }
                        )
                    }
                    BasicText(
                        "navigate to first",
                        Modifier.clickable {
                            navController.onFirstClicked()
                        }
                    )
                    BasicText(
                        "navigate to second",
                        Modifier.clickable {
                            navController.onSecondClicked()
                        }
                    )
                    BasicText(
                        "navigate to third",
                        Modifier.clickable {
                            navController.onThirdClicked()
                        }
                    )
                }
            }
        }

        composeTestRule.onNodeWithText("value: first 1, count: 0").assertExists()
        composeTestRule.onNodeWithText("navigate back").assertDoesNotExist()

        composeTestRule.onNodeWithText("increment").performClick()

        composeTestRule.onNodeWithText("value: first 1, count: 1").assertExists()

        composeTestRule.onNodeWithText("navigate to second").performClick()

        composeTestRule.onNodeWithText("value: second 1, count: 0").assertExists()

        composeTestRule.onNodeWithText("increment").performClick()

        composeTestRule.onNodeWithText("value: second 1, count: 1").assertExists()

        composeTestRule.onNodeWithText("navigate back").performClick()

        composeTestRule.onNodeWithText("value: first 1, count: 1").assertExists()

        composeTestRule.onNodeWithText("navigate to second").performClick()

        composeTestRule.onNodeWithText("value: second 1, count: 1").assertExists()
    }
}

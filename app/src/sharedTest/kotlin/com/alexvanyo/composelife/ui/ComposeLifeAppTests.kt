package com.alexvanyo.composelife.ui

import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.test.BaseAndroidTest
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class ComposeLifeAppTests : BaseAndroidTest() {

    @get:Rule(order = 1)
    val composeTestRule = createAndroidComposeRule<MainActivity>()

    @BindValue
    val fileProvider = preferencesRule.fileProvider

    @Test
    fun app_does_not_crash() = runTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.awaitIdle()
    }

    @Test
    fun app_does_not_crash_when_recreating() = runTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.activityRule.scenario.recreate()

        composeTestRule.awaitIdle()
    }
}

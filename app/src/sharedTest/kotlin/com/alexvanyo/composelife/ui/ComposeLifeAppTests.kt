package com.alexvanyo.composelife.ui

import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import com.alexvanyo.composelife.MainActivity
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.test.BaseHiltTest
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import org.junit.Test

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class ComposeLifeAppTests : BaseHiltTest<MainActivity>(MainActivity::class.java) {

    @Test
    fun app_does_not_crash() = runAppTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.waitForIdle()
    }

    @Test
    fun app_does_not_crash_when_recreating() = runAppTest {
        composeTestRule.onNodeWithContentDescription(context.getString(R.string.pause)).performClick()

        composeTestRule.activityRule.scenario.recreate()

        composeTestRule.waitForIdle()
    }
}

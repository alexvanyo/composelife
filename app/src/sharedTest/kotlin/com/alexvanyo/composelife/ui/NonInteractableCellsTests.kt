package com.alexvanyo.composelife.ui

import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class NonInteractableCellsTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun non_interactable_cells_preview() {
        composeTestRule.setContent {
            NonInteractableCellsPreview()
        }
    }
}

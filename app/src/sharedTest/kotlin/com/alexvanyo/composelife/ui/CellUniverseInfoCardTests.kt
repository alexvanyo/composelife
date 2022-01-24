package com.alexvanyo.composelife.ui

import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class CellUniverseInfoCardTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun collapsed_preview() {
        composeTestRule.setContent {
            CellUniverseInfoCardCollapsedPreview()
        }
    }

    @Test
    fun fully_collapsed_preview() {
        composeTestRule.setContent {
            CellUniverseInfoCardFullyCollapsedPreview()
        }
    }

    @Test
    fun expanded_preview() {
        composeTestRule.setContent {
            CellUniverseInfoCardExpandedPreview()
        }
    }
}

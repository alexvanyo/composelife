/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsEnabled
import androidx.compose.ui.test.assertIsNotEnabled
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performTextInput
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.test.runComposeUiTest
import com.alexvanyo.composelife.ui.settings.resources.AddPatternCollection
import com.alexvanyo.composelife.ui.settings.resources.Delete
import com.alexvanyo.composelife.ui.settings.resources.SourceUrlLabel
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.TimeZoneHolder
import kotlinx.coroutines.awaitCancellation
import kotlinx.datetime.TimeZone
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Clock

@OptIn(ExperimentalTestApi::class)
class PatternCollectionsUiTests : BaseKmpTest() {

    private val testClock = Clock.System
    private val testTimeZoneHolder = object : TimeZoneHolder {
        override val timeZone: TimeZone = TimeZone.UTC
        override suspend fun update(): Nothing {
            awaitCancellation()
        }
    }

    @Test
    fun add_pattern_collection_button_is_disabled_for_empty_url() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(emptyList()),
                            addPatternCollection = {},
                            deletePatternCollection = {},
                        )
                    }
                }
            }

            onNodeWithText(resolver(Strings.AddPatternCollection))
                .assertIsNotEnabled()
        }
    }

    @Test
    fun add_pattern_collection_button_is_disabled_for_invalid_url() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(emptyList()),
                            addPatternCollection = {},
                            deletePatternCollection = {},
                        )
                    }
                }
            }

            onNodeWithText(resolver(Strings.SourceUrlLabel))
                .performTextInput("not a url")

            onNodeWithText(resolver(Strings.AddPatternCollection))
                .assertIsNotEnabled()
        }
    }

    @Test
    fun add_pattern_collection_button_is_enabled_for_valid_url() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(emptyList()),
                            addPatternCollection = {},
                            deletePatternCollection = {},
                        )
                    }
                }
            }

            onNodeWithText(resolver(Strings.SourceUrlLabel))
                .performTextInput("https://example.com")

            onNodeWithText(resolver(Strings.AddPatternCollection))
                .assertIsEnabled()
        }
    }

    @Test
    fun pattern_collections_are_displayed_correctly() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            val patternCollection = PatternCollection(
                id = PatternCollectionId(1),
                sourceUrl = "https://example.com/1",
                lastSuccessfulSynchronizationTimestamp = null,
                lastUnsuccessfulSynchronizationTimestamp = null,
                synchronizationFailureMessage = null,
                isSynchronizing = false,
            )

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(listOf(patternCollection)),
                            addPatternCollection = {},
                            deletePatternCollection = {},
                        )
                    }
                }
            }

            onNodeWithText("https://example.com/1")
                .assertExists()
        }
    }

    @Test
    fun deleting_pattern_collection_works_correctly() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            val patternCollectionId = PatternCollectionId(1)
            val patternCollection = PatternCollection(
                id = patternCollectionId,
                sourceUrl = "https://example.com/1",
                lastSuccessfulSynchronizationTimestamp = null,
                lastUnsuccessfulSynchronizationTimestamp = null,
                synchronizationFailureMessage = null,
                isSynchronizing = false,
            )

            var deletedId: PatternCollectionId? = null

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(listOf(patternCollection)),
                            addPatternCollection = {},
                            deletePatternCollection = { deletedId = it },
                        )
                    }
                }
            }

            onNodeWithContentDescription(resolver(Strings.Delete))
                .performClick()

            assertEquals(patternCollectionId, deletedId)
        }
    }

    @Test
    fun adding_pattern_collection_works_correctly() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            var addedUrl: String? = null

            setContent {
                resolver = parameterizedStringResolver()
                with(testClock) {
                    with(testTimeZoneHolder) {
                        PatternCollectionsUi(
                            patternCollectionsState = ResourceState.Success(emptyList()),
                            addPatternCollection = { addedUrl = it },
                            deletePatternCollection = {},
                        )
                    }
                }
            }

            onNodeWithText(resolver(Strings.SourceUrlLabel))
                .performTextInput("https://example.com")

            onNodeWithText(resolver(Strings.AddPatternCollection))
                .performClick()

            waitForIdle()
            assertEquals("https://example.com", addedUrl)
        }
    }
}

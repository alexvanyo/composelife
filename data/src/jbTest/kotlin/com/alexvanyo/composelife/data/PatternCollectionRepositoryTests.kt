/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.network.FakeRequestHandler
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.test.BaseInjectTest
import io.ktor.client.engine.mock.respond
import kotlinx.coroutines.async
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.runCurrent
import kotlinx.datetime.Instant
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@OptIn(ExperimentalCoroutinesApi::class)
class PatternCollectionRepositoryTests : BaseInjectTest<
    TestComposeLifeApplicationComponent,
    TestComposeLifeApplicationEntryPoint
    >(
    TestComposeLifeApplicationComponent::createComponent,
) {
    private val entryPoint: TestComposeLifeApplicationEntryPoint get() = applicationComponent.kmpGetEntryPoint()

    private val patternCollectionRepository: PatternCollectionRepository
        get() = entryPoint.patternCollectionRepository

    private val patternCollectionQueries get() = entryPoint.patternCollectionQueries

    private val testDispatcher get() = entryPoint.generalTestDispatcher

    private val fakeRequestHandler: FakeRequestHandler get() = entryPoint.fakeRequestHandler

    @Test
    fun pattern_collection_is_empty_initially() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        runCurrent()

        assertEquals(
            ResourceState.Success(emptyList()),
            patternCollectionRepository.collections,
        )
    }

    @Test
    fun adding_pattern_collection_updates_collections() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )

        runCurrent()

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = null,
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = false,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )
    }

    @Test
    fun after_adding_pattern_collection_synchronization_updates() = runAppTest(testDispatcher) {
        backgroundScope.launch {
            patternCollectionRepository.observePatternCollections()
        }

        val patternCollectionId = patternCollectionRepository.addPatternCollection(
            sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
        )


        val synchronizationJob = async {
            patternCollectionRepository.synchronizePatternCollections()
        }

        runCurrent()

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = null,
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = true,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )

        fakeRequestHandler.addRequestHandler { request ->
            assertEquals("https://alex.vanyo.dev/composelife/patterns.zip", request.url.toString())
            respond(
                this::class.java
                    .getResource("/patternfiles/patterns.zip")!!
                    .readBytes()
            )
        }

        assertTrue(synchronizationJob.await())

        assertEquals(
            ResourceState.Success(
                listOf(
                    PatternCollection(
                        id = patternCollectionId,
                        sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                        lastSuccessfulSynchronizationTimestamp = Instant.fromEpochSeconds(0),
                        lastUnsuccessfulSynchronizationTimestamp = null,
                        synchronizationFailureMessage = null,
                        isSynchronizing = false,
                    )
                )
            ),
            patternCollectionRepository.collections,
        )
    }
}

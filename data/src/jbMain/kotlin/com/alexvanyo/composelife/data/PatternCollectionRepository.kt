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
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.resourcestate.ResourceState

interface PatternCollectionRepository {
    /**
     * An observable list of all [PatternCollection]s backed by snapshot state.
     *
     * This will only update while [observePatternCollections] is being called.
     */
    val collections: ResourceState<List<PatternCollection>>

    /**
     * Signals to update [collections] since it is being read.
     *
     * This method will never return, so cancel it when no longer wanting to observe [collections].
     */
    suspend fun observePatternCollections(): Nothing

    /**
     * Adds a new pattern collection with the given [sourceUrl].
     */
    suspend fun addPatternCollection(
        sourceUrl: String,
    ): PatternCollectionId

    /**
     * Deletes the pattern collection with the given [PatternCollectionId].
     */
    suspend fun deletePatternCollection(
        patternCollectionId: PatternCollectionId,
    )

    /**
     * Attempts to fetch and synchronize all pattern collections, and extract the patterns from the downloaded
     * archives.
     *
     * This method returns `true` when all synchronization has finished successfully, otherwise it returns `false`.
     */
    suspend fun synchronizePatternCollections(): Boolean
}

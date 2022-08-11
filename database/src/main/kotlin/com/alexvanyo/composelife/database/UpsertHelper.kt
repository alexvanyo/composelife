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

package com.alexvanyo.composelife.database

suspend fun <T> upsert(
    entities: List<T>,
    idGetter: (T) -> Long,
    insertOrIgnoreEntities: suspend (List<T>) -> List<Long>,
    updateEntities: suspend (List<T>) -> Unit,
): List<Long> {
    val insertResults = insertOrIgnoreEntities(entities)
    val entityIds = entities.zip(insertResults) { entity, insertResult ->
        if (insertResult == -1L) idGetter(entity) else insertResult
    }
    updateEntities(
        entities.zip(insertResults) { entity, insertResult ->
            entity.takeIf { insertResult == -1L }
        }
            .filterNotNull(),
    )
    return entityIds
}

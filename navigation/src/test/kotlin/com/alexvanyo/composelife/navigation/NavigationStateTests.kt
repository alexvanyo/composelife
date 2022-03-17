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

import org.junit.jupiter.api.Test
import java.util.UUID
import kotlin.test.assertEquals

class NavigationStateTests {

    @Test
    fun `current entry is correct`() {
        val id1 = UUID.randomUUID()
        val id2 = UUID.randomUUID()
        val entry1 = object : NavigationEntry {
            override val id: UUID = id1
        }
        val entry2 = object : NavigationEntry {
            override val id: UUID = id2
        }

        val navigationState = object : NavigationState<NavigationEntry> {
            override val entryMap get() = listOf(entry1, entry2).associateBy { it.id }
            override val currentEntryId get() = id2
        }

        assertEquals(
            entry2,
            navigationState.currentEntry
        )
    }
}

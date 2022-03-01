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

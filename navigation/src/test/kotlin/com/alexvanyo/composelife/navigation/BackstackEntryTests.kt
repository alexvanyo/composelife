package com.alexvanyo.composelife.navigation

import org.junit.jupiter.api.Test
import java.util.UUID
import kotlin.test.assertEquals

class BackstackEntryTests {

    private val id1 = UUID.randomUUID()
    private val id2 = UUID.randomUUID()
    private val id3 = UUID.randomUUID()
    private val id4 = UUID.randomUUID()
    private val entry1 = BackstackEntry("a", null, id1)
    private val entry2 = BackstackEntry("b", entry1, id2)
    private val entry3 = BackstackEntry("c", entry2, id3)
    private val entry4 = BackstackEntry("d", entry3, id4)

    @Test
    fun `entry 1 iterable is correct`() {
        assertEquals(
            listOf(entry1),
            entry1.iterator().asSequence().toList()
        )
    }

    @Test
    fun `entry 2 iterable is correct`() {
        assertEquals(
            listOf(entry2, entry1),
            entry2.iterator().asSequence().toList()
        )
    }

    @Test
    fun `entry 3 iterable is correct`() {
        assertEquals(
            listOf(entry3, entry2, entry1),
            entry3.iterator().asSequence().toList()
        )
    }

    @Test
    fun `entry 4 iterable is correct`() {
        assertEquals(
            listOf(entry4, entry3, entry2, entry1),
            entry4.iterator().asSequence().toList()
        )
    }
}

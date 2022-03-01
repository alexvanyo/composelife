package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.mutableStateMapOf
import org.junit.jupiter.api.Test
import java.util.UUID
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull

class BackstackNavigationTests {

    private val id1 = UUID.randomUUID()
    private val id2 = UUID.randomUUID()
    private val id3 = UUID.randomUUID()
    private val id4 = UUID.randomUUID()
    private val entry1 = BackstackEntry("a", null, id1)
    private val entry2 = BackstackEntry("b", entry1, id2)
    private val entry3 = BackstackEntry("c", entry2, id3)
    private val entry4 = BackstackEntry("d", entry3, id4)

    private val mutableBackstackMap: MutableBackstackMap<String> = mutableStateMapOf(
        id1 to entry1,
        id2 to entry2,
        id3 to entry3,
        id4 to entry4,
    )

    @Test
    fun `pop backstack is correct`() {
        val newId = mutableBackstackMap.popBackstack(id4)

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id3, newId)
    }

    @Test
    fun `pop backstack with one entry throws exception`() {
        mutableBackstackMap.popBackstack(id4)
        mutableBackstackMap.popBackstack(id3)
        mutableBackstackMap.popBackstack(id2)

        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popBackstack(id1)
        }
    }

    @Test
    fun `pop up to with id non inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            id = id2
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id2, newId)
    }

    @Test
    fun `pop up to with id inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            id = id2,
            inclusive = true
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id1, newId)
    }

    @Test
    fun `pop up to with no matching id throws exception`() {
        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popUpTo(
                currentEntryId = id4,
                id = UUID.randomUUID(),
            )
        }
    }

    @Test
    fun `pop up to inclusive on last entry throws exception`() {
        assertFailsWith<IllegalStateException> {
            mutableBackstackMap.popUpTo(
                currentEntryId = id4,
                id = id1,
                inclusive = true
            )
        }
    }

    @Test
    fun `pop up to with value predicate non inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            predicate = { it == "b" }
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id2, newId)
    }

    @Test
    fun `pop up to with value inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            predicate = { it == "b" },
            inclusive = true
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id1, newId)
    }

    @Test
    fun `pop up to with entry predicate non inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            entryPredicate = { it.value == "b" }
        )

        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id2, newId)
    }

    @Test
    fun `pop up to with entry predicate inclusive is correct`() {
        val newId = mutableBackstackMap.popUpTo(
            currentEntryId = id4,
            entryPredicate = { it.value == "b" },
            inclusive = true
        )

        assertEquals(
            mapOf(
                id1 to entry1,
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id1, newId)
    }

    @Test
    fun `navigate with raw value is correct`() {
        val id5 = UUID.randomUUID()
        val newId = mutableBackstackMap.navigate(
            currentEntryId = id4,
            value = "e",
            id = id5,
        )

        val entry5 = mutableBackstackMap[newId]

        assertNotNull(entry5)
        assertEquals("e", entry5.value)
        assertEquals(id5, entry5.id)
        assertEquals(entry4, entry5.previous)
        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3,
                id4 to entry4,
                id5 to entry5
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id5, newId)
    }

    @Test
    fun `navigate with value factory is correct`() {
        val id5 = UUID.randomUUID()
        val newId = mutableBackstackMap.navigate(
            currentEntryId = id4,
            valueFactory = { it.value + "2" },
            id = id5,
        )

        val entry5 = mutableBackstackMap[newId]

        assertNotNull(entry5)
        assertEquals("d2", entry5.value)
        assertEquals(id5, entry5.id)
        assertEquals(entry4, entry5.previous)
        assertEquals(
            mapOf(
                id1 to entry1,
                id2 to entry2,
                id3 to entry3,
                id4 to entry4,
                id5 to entry5
            ),
            mutableBackstackMap.toMap()
        )
        assertEquals(id5, newId)
    }
}

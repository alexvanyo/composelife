package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.ui.test.junit4.StateRestorationTester
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import java.util.UUID
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

@RunWith(AndroidJUnit4::class)
class BackstackStateTests {

    private val id1 = UUID.randomUUID()
    private val id2 = UUID.randomUUID()
    private val id3 = UUID.randomUUID()
    private val id4 = UUID.randomUUID()

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun backstack_state_with_basic_value_is_saved_correctly() {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        var backstackMap: MutableBackstackMap<String>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                val entry1 = BackstackEntry(
                    value = "a",
                    previous = null,
                    id = id1
                )
                val entry2 = BackstackEntry(
                    value = "b",
                    previous = entry1,
                    id = id2
                )
                val entry3 = BackstackEntry(
                    value = "c",
                    previous = entry2,
                    id = id3
                )
                val entry4 = BackstackEntry(
                    value = "d",
                    previous = entry3,
                    id = id4
                )

                listOf(entry1, entry2, entry3, entry4)
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(4, restoredBackstackMap.size)
        assertEquals("a", restoredBackstackMap[id1]?.value)
        assertEquals("b", restoredBackstackMap[id2]?.value)
        assertEquals("c", restoredBackstackMap[id3]?.value)
        assertEquals("d", restoredBackstackMap[id4]?.value)
    }

    @Test
    fun backstack_state_with_saver_factory_is_saved_correctly() {
        val stateRestorationTester = StateRestorationTester(composeTestRule)

        var backstackMap: MutableBackstackMap<TestEntryType>? = null

        stateRestorationTester.setContent {
            val initialBackstackEntries = remember {
                val entry1 = BackstackEntry(
                    value = TestEntryType(
                        value = "a",
                        previous = null
                    ),
                    previous = null,
                    id = id1
                )
                val entry2 = BackstackEntry(
                    value = TestEntryType(
                        value = "b",
                        previous = entry1.value
                    ),
                    previous = entry1,
                    id = id2
                )
                val entry3 = BackstackEntry(
                    value = TestEntryType(
                        value = "c",
                        previous = entry2.value
                    ),
                    previous = entry2,
                    id = id3
                )
                val entry4 = BackstackEntry(
                    value = TestEntryType(
                        value = "d",
                        previous = entry3.value
                    ),
                    previous = entry3,
                    id = id4
                )

                listOf(entry1, entry2, entry3, entry4)
            }

            backstackMap = rememberBackstackMap(
                initialBackstackEntries = initialBackstackEntries,
                backstackValueSaverFactory = { entry ->
                    Saver(
                        save = { it.value },
                        restore = {
                            TestEntryType(
                                value = it as String,
                                previous = entry?.value
                            )
                        }
                    )
                }
            )
        }

        assertNotNull(backstackMap)
        backstackMap = null

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restoredBackstackMap = assertNotNull(backstackMap)
        assertEquals(4, restoredBackstackMap.size)
        assertEquals("a", restoredBackstackMap[id1]?.value?.fullValue)
        assertEquals("ab", restoredBackstackMap[id2]?.value?.fullValue)
        assertEquals("abc", restoredBackstackMap[id3]?.value?.fullValue)
        assertEquals("abcd", restoredBackstackMap[id4]?.value?.fullValue)
    }
}

class TestEntryType(
    val value: String,
    val previous: TestEntryType?
) {
    val fullValue: String get() = previous?.fullValue.orEmpty() + value
}

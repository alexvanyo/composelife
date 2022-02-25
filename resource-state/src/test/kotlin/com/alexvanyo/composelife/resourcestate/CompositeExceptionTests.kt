package com.alexvanyo.composelife.resourcestate

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class CompositeExceptionTests {

    @Test
    fun `empty constructor throws exception`() {
        assertFailsWith<IllegalArgumentException> {
            CompositeException()
        }
    }

    @Test
    fun `single exception constructor throws exception`() {
        assertFailsWith<IllegalArgumentException> {
            CompositeException(Exception())
        }
    }

    @Test
    fun `vararg constructor creates expected exception`() {
        val exception1 = Exception()
        val exception2 = Exception()

        val compositeException = CompositeException(exception1, exception2)

        assertEquals("2 exceptions occurred.", compositeException.message)
        assertEquals(exception1, compositeException.cause)
        assertEquals(listOf(exception1, exception2), compositeException.exceptions)
    }
}

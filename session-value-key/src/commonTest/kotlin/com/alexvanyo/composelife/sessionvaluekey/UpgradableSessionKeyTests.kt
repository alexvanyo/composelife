/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.sessionvaluekey

import java.util.UUID
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

class UpgradableSessionKeyTests {

    @Test
    fun a_b_is_not_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertNotEquals(
            UpgradableSessionKey(a),
            UpgradableSessionKey(b),
        )
    }

    @Test
    fun a_bc_is_not_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertNotEquals(
            UpgradableSessionKey(a),
            UpgradableSessionKey(b, c),
        )
    }

    @Test
    fun ab_c_is_not_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertNotEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(c),
        )
    }

    @Test
    fun ab_cd_is_not_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()
        val d = UUID.randomUUID()

        assertNotEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(c, d),
        )
    }

    @Test
    fun a_a_is_equal() {
        val a = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a),
            UpgradableSessionKey(a),
        )
    }

    @Test
    fun a_ab_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a),
            UpgradableSessionKey(a, b),
        )
    }

    @Test
    fun b_ab_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(b),
            UpgradableSessionKey(a, b),
        )
    }

    @Test
    fun ab_a_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(a),
        )
    }

    @Test
    fun ab_b_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(b),
        )
    }

    @Test
    fun ab_ab_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(a, b),
        )
    }

    @Test
    fun ab_ba_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(b, a),
        )
    }

    @Test
    fun ab_bc_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(b, c),
        )
    }

    @Test
    fun ab_cb_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(c, b),
        )
    }

    @Test
    fun ab_ac_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(a, c),
        )
    }

    @Test
    fun ab_ca_is_equal() {
        val a = UUID.randomUUID()
        val b = UUID.randomUUID()
        val c = UUID.randomUUID()

        assertEquals(
            UpgradableSessionKey(a, b),
            UpgradableSessionKey(c, a),
        )
    }
}

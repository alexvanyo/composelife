/*
 * Copyright 2026 The Android Open Source Project
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

/*
 * Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */
package lean.runtime

import kotlin.jvm.JvmField
import kotlin.jvm.JvmStatic

/**
 * Representation of a Lean Nat (arbitrary precision natural number).
 * Small nats are stored as non-negative 64-bit integers.
 */
public final class LeanNat(@JvmField public val smallVal: Long,) : LeanObject() {

    public override val tag: Int get() = smallVal.toInt()

    override fun toString(): String = smallVal.toString()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is LeanNat) return false
        return smallVal == other.smallVal
    }

    override fun hashCode(): Int = smallVal.hashCode()

    companion object {
        @JvmStatic
        public val ZERO: LeanNat = LeanNat(0L)

        @JvmStatic
        public val ONE: LeanNat = LeanNat(1L)

        @JvmStatic
        public fun ofLong(v: Long): LeanNat = if (v == 0L) ZERO else if (v == 1L) {
            ONE
        } else {
            LeanNat(v)
        }

        @JvmStatic
        public fun add(a: LeanNat, b: LeanNat): LeanNat = LeanNat(a.smallVal + b.smallVal)

        @JvmStatic
        public fun sub(a: LeanNat, b: LeanNat): LeanNat =
            LeanNat(if (a.smallVal < b.smallVal) 0L else a.smallVal - b.smallVal)

        @JvmStatic
        public fun mul(a: LeanNat, b: LeanNat): LeanNat = LeanNat(a.smallVal * b.smallVal)

        @JvmStatic
        public fun div(a: LeanNat, b: LeanNat): LeanNat =
            if (b.smallVal == 0L) ZERO else LeanNat(a.smallVal / b.smallVal)

        @JvmStatic
        public fun mod(a: LeanNat, b: LeanNat): LeanNat =
            if (b.smallVal == 0L) ZERO else LeanNat(a.smallVal % b.smallVal)

        @JvmStatic
        public fun ble(a: LeanNat, b: LeanNat): Boolean = a.smallVal <= b.smallVal

        @JvmStatic
        public fun blt(a: LeanNat, b: LeanNat): Boolean = a.smallVal < b.smallVal
    }
}

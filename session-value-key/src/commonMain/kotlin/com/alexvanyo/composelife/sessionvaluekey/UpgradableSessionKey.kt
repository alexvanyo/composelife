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

/**
 * An upgradable key made of [UUID]s.
 *
 * A [UpgradableSessionKey] is equal to another [UpgradableSessionKey] if any of the [UUID]s used to construct
 * this [UpgradableSessionKey] match any of the [UUID]s used to construct the other [UpgradableSessionKey].
 */
class UpgradableSessionKey private constructor(
    private val a: UUID,
    private val b: UUID?,
    @Suppress("UNUSED_PARAMETER")
    unused: Unit,
) {
    constructor(
        a: UUID,
    ) : this(a, null, Unit)

    constructor(
        a: UUID,
        b: UUID,
    ) : this(a, b, Unit)

    override fun equals(other: Any?): Boolean =
        other is UpgradableSessionKey && (
            (a == other.a || a == other.b) ||
                (b != null && (b == other.a || b == other.b))
            )

    /**
     * This is a bad hashcode function, but we can't do any better and preserve the contract with [equals].
     */
    override fun hashCode(): Int = 1
}

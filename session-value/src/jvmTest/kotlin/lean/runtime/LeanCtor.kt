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
 * Representation of a Lean inductive datatype constructor.
 * Contains:
 * - [tag]: Constructor index (cidx)
 * - [objs]: Object fields (pointers to other LeanObject instances)
 * - [scalars]: Packed 64-bit scalar fields (UInt8..UInt64, Float, USize)
 */
public final class LeanCtor(
    public override val tag: Int,
    @JvmField public val objs: Array<LeanObject?> = EMPTY_OBJS,
    @JvmField public val scalars: LongArray = EMPTY_SCALARS,
) : LeanObject() {

    public fun getObj(index: Int): LeanObject? = objs[index]
    public fun setObj(index: Int, value: LeanObject?) {
        objs[index] = value
    }

    public fun getScalar(offset: Int): Long =
        if (offset in scalars.indices) scalars[offset] else 0L

    public fun setScalar(offset: Int, value: Long) {
        if (offset in scalars.indices) {
            scalars[offset] = value
        }
    }

    override fun toString(): String =
        "LeanCtor(tag=$tag, objs=${objs.contentToString()}, scalars=${scalars.contentToString()})"

    companion object {
        private val EMPTY_SCALARS = LongArray(0)
        private val EMPTY_OBJS = emptyArray<LeanObject?>()

        @JvmStatic
        public fun alloc(tag: Int, numObjs: Int, numScalars: Int): LeanCtor {
            val objs = if (numObjs == 0) EMPTY_OBJS else arrayOfNulls(numObjs)
            val scalars = if (numScalars == 0) EMPTY_SCALARS else LongArray(numScalars)
            return LeanCtor(tag, objs, scalars)
        }
    }
}

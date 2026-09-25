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

import kotlin.jvm.JvmStatic

/**
 * JVM-specific Lean runtime utilities and MethodHandle-based closures.
 */
public object LeanRuntimeJVM {

    @JvmStatic
    public fun boxUInt8(v: Byte): LeanObject = LeanNat.ofLong((v.toInt() and 0xFF).toLong())

    @JvmStatic
    public fun boxUInt16(v: Short): LeanObject = LeanNat.ofLong((v.toInt() and 0xFFFF).toLong())

    @JvmStatic
    public fun boxUInt32(v: Int): LeanObject = LeanNat.ofLong(v.toLong() and 0xFFFFFFFFL)

    @JvmStatic
    public fun boxUInt64(v: Long): LeanObject = LeanNat.ofLong(v)

    @JvmStatic
    public fun boxUSize(v: Long): LeanObject = LeanNat.ofLong(v)

    @JvmStatic
    public fun unboxUInt32(obj: LeanObject?): Int = when (obj) {
            is LeanNat -> obj.smallVal.toInt()
            else -> 0
        }

    @JvmStatic
    public fun unboxUInt64(obj: LeanObject?): Long = when (obj) {
            is LeanNat -> obj.smallVal
            else -> 0L
        }

    @JvmStatic
    public fun printString(str: LeanString) {
        System.out.print(str.toString())
    }

    @JvmStatic
    public fun printLnString(str: LeanString) {
        System.out.println(str.toString())
    }
}

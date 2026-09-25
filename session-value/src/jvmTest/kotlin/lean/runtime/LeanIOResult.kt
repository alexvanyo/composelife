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
 * Representation of IO results in Lean:
 * EStateM.Result ε σ α = ok (a : α) (s : σ) | error (e : ε) (s : σ)
 */
public final class LeanIOResult(
    public val isOk: Boolean,
    @JvmField public val value: LeanObject?,
    @JvmField public val error: LeanObject?,
) : LeanObject() {

    companion object {
        @JvmStatic
        public fun ok(value: LeanObject?): LeanIOResult = LeanIOResult(true, value, null)

        @JvmStatic
        public fun error(error: LeanObject?): LeanIOResult = LeanIOResult(false, null, error)
    }
}

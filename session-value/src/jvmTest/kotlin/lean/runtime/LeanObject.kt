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

/**
 * Base class for all Lean heap objects in the runtime.
 */
public abstract class LeanObject {
    /** Constructor or object tag (0 for scalar/unboxed or default). */
    public open val tag: Int get() = 0

    /** True if this object represents an unboxed/scalar value. */
    public open val isScalar: Boolean get() = false

    override fun equals(other: Any?): Boolean = this === other

    override fun hashCode(): Int = super.hashCode()
}

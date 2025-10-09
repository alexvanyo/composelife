/*
 * Copyright 2020 Livefront
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

package com.livefront.sealedenum.internal.common

import com.squareup.kotlinpoet.KModifier

/**
 * A restricted enumeration of visibilities for use with sealed classes. Due to generating code that is in a different
 * file, we can only reasonably work with sealed classes and companion objects that are public or internal.
 */
public enum class Visibility(public val kModifier: KModifier) {
    PUBLIC(KModifier.PUBLIC),
    INTERNAL(KModifier.INTERNAL);
}

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

package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.symbol.KSAnnotation
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.TreeTraversalOrder

/**
 * A constructable version of [GenSealedEnum].
 */
public data class GenSealedEnumHolder(
    val traversalOrder: TreeTraversalOrder,
    val generateEnum: Boolean,
) {

    public companion object {
        public fun fromKSAnnotation(ksAnnotation: KSAnnotation): GenSealedEnumHolder {
            val traversalOrderQualifiedName = ksAnnotation.arguments.find {
                it.name?.asString() == "traversalOrder"
            }?.value.toString()

            @Suppress("SwallowedException")
            val traversalOrder = try {
                @Suppress("UnsafeCallOnNullableType")
                TreeTraversalOrder.valueOf(
                    traversalOrderQualifiedName.removePrefix(
                        "${TreeTraversalOrder::class.qualifiedName!!}."
                    )
                )
            } catch (exception: IllegalArgumentException) {
                TreeTraversalOrder.IN_ORDER
            }

            val generateEnum = ksAnnotation.arguments.find {
                it.name?.asString() == "generateEnum"
            }?.value.toString().toBoolean()

            return GenSealedEnumHolder(
                traversalOrder,
                generateEnum
            )
        }
    }
}

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

package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.symbol.KSClassDeclaration
import com.google.devtools.ksp.symbol.Variance
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.STAR
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.ksp.toClassName
import com.squareup.kotlinpoet.ksp.toTypeName

internal fun KSClassDeclaration.toTypeName(argumentList: List<TypeName> = emptyList()): TypeName {
    val className = toClassName()
    return if (argumentList.isNotEmpty()) {
        className.parameterizedBy(argumentList)
    } else {
        className
    }
}

/**
 * A mapping of [KSClassDeclaration.typeParameters] to [TypeName]s.
 *
 * Rather than returning variable names, they are converted into a [TypeName] that can be directly specified in an
 * interface.
 *
 * In particular, single invariant types can be replaced with the type directly. In all other cases (multiple bounds,
 * other types of variance) the only thing we can do is wildcard the type.
 */
internal fun KSClassDeclaration.wildcardedTypeNames(): List<TypeName> =
    typeParameters.map {
        val bounds = it.bounds.toList()

        if (bounds.size == 1) {
            when (it.variance) {
                Variance.INVARIANT -> bounds[0].resolve().toTypeName()
                else -> STAR
            }
        } else {
            STAR
        }
    }

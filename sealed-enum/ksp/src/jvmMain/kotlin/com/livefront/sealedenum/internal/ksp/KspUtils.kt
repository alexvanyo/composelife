package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.symbol.KSAnnotated
import com.google.devtools.ksp.symbol.KSAnnotation
import com.google.devtools.ksp.symbol.KSClassDeclaration
import com.google.devtools.ksp.symbol.KSType

internal fun KSClassDeclaration.asType(): KSType = asType(emptyList())

internal fun KSAnnotated.findAnnotationsWithType(target: KSType): Sequence<KSAnnotation> =
    annotations.filter { it.annotationType.resolve() == target }

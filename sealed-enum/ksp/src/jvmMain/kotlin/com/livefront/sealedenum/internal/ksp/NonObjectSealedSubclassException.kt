package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.symbol.KSNode

/**
 * An exception that indicates that sealed class has a non-object subclass.
 */
public class NonObjectSealedSubclassException(public val ksNode: KSNode) : Exception()

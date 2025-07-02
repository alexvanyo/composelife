package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.symbol.KSNode

/**
 * An exception that indicates that a sealed subclass has an invalid visibility.
 */
public class InvalidSubclassVisibilityException(public val ksNode: KSNode) : Exception()

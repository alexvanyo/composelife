package com.livefront.sealedenum.internal.common.spec

import com.squareup.kotlinpoet.OriginatingElementsHolder
import javax.lang.model.element.Element

/**
 * Adds [originatingElement] as an originating element if it is non-null.
 */
internal fun <T : OriginatingElementsHolder.Builder<T>> T.maybeAddOriginatingElement(originatingElement: Element?): T =
    originatingElement?.let(::addOriginatingElement) ?: this

package com.livefront.sealedenum.internal.common

import com.livefront.sealedenum.internal.common.SealedClassNode.Object
import com.livefront.sealedenum.internal.common.SealedClassNode.SealedClass
import com.livefront.sealedenum.internal.common.spec.SealedObject

/**
 * An internal tree structure representing a sealed class and its sealed subclasses.
 *
 * A node can either be a [Object] (a leaf node) or a [SealedClass] (which might be a non-leaf node).
 */
public sealed class SealedClassNode {

    /**
     * The leaf node of the sealed class tree, which represents an object subclass.
     *
     * The object's name is [className]
     */
    public data class Object(public val className: SealedObject) : SealedClassNode()

    /**
     * A node representing a subclass sealed class. This node may have additional children in [sealedSubclasses],
     * or could be a leaf itself if [sealedSubclasses] is empty.
     */
    public data class SealedClass(public val sealedSubclasses: List<SealedClassNode>) : SealedClassNode()
}

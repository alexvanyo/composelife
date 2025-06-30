package com.livefront.sealedenum

/**
 * An enum specifying the traversal order for the list of sealed objects.
 */
public enum class TreeTraversalOrder {
    /**
     * All objects that are direct children of a sealed class will be listed before objects in subclasses that are
     * themselves sealed.
     */
    PRE_ORDER,

    /**
     * Objects will be included in-order, based on the declaration of the sealed class. If all subclasses are
     * declared as enclosed elements inside sealed classes, this order will match the the order from top-to-bottom in
     * which the objects are declared.
     */
    IN_ORDER,

    /**
     * All objects that are direct children of a sealed class will be listed after objects in subclasses that are
     * themselves sealed.
     */
    POST_ORDER,

    /**
     * Objects are listed in order based on how deeply they are nested within the sealed subclass.
     */
    LEVEL_ORDER
}

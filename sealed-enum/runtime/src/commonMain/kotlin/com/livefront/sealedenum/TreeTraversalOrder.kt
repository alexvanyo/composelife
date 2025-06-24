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

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

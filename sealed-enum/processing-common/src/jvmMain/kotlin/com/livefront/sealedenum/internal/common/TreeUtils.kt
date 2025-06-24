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

import com.livefront.sealedenum.TreeTraversalOrder
import com.squareup.kotlinpoet.ClassName
import java.util.ArrayDeque

/**
 * An internal function to traverse the tree rooted at [sealedClassNode] with the prescribed [treeTraversalOrder],
 * returning a list of [ClassName]s representing all [SealedClassNode.Object]s in the tree.
 * Duplicates are removed, and only the first occurrence of each [ClassName] is preserved.
 */
public fun getSealedObjectsFromNode(
    treeTraversalOrder: TreeTraversalOrder,
    sealedClassNode: SealedClassNode.SealedClass
): List<ClassName> {
    // Set up the deque for iterative processing.
    // For level order traversal, this will be used as a queue, and for all other traversal this will be used as a stack
    val nodeDeque = ArrayDeque<SealedClassNode>().apply {
        add(sealedClassNode)
    }

    val sealedObjects = mutableListOf<ClassName>()

    while (nodeDeque.isNotEmpty()) {
        when (val node = nodeDeque.pop()) {
            is SealedClassNode.Object -> sealedObjects.add(node.className)
            is SealedClassNode.SealedClass ->
                when (treeTraversalOrder) {
                    TreeTraversalOrder.PRE_ORDER -> {
                        // We push any sealed classes first, so that they come after the sealed classes in the stack
                        // We reverse each set so that the original ordering is preserved within each category
                        node.sealedSubclasses.filterIsInstance<SealedClassNode.SealedClass>()
                            .reversed()
                            .forEach(nodeDeque::push)
                        node.sealedSubclasses.filterIsInstance<SealedClassNode.Object>()
                            .reversed()
                            .forEach(nodeDeque::push)
                    }
                    TreeTraversalOrder.IN_ORDER -> {
                        // For in order, we don't change the order of the children, apart from reversing our insertion
                        // order so that the first child ends up at the top of the stack.
                        node.sealedSubclasses.reversed().forEach(nodeDeque::push)
                    }
                    TreeTraversalOrder.POST_ORDER -> {
                        // We push any leaf objects first, so that they come after the sealed classes in the stack
                        // We reverse each set so that the original ordering is preserved within each category
                        node.sealedSubclasses.filterIsInstance<SealedClassNode.Object>()
                            .reversed()
                            .forEach(nodeDeque::push)
                        node.sealedSubclasses.filterIsInstance<SealedClassNode.SealedClass>()
                            .reversed()
                            .forEach(nodeDeque::push)
                    }
                    TreeTraversalOrder.LEVEL_ORDER -> {
                        // For level order, we process children as a queue
                        node.sealedSubclasses.forEach(nodeDeque::addLast)
                    }
                }
        }
    }

    return sealedObjects.distinct()
}

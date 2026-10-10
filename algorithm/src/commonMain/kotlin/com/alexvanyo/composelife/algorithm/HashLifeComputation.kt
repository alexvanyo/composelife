/*
 * Copyright 2026 The Android Open Source Project
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

@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.model.LeafNode
import com.alexvanyo.composelife.model.MacroCell

/**
 * Computes the next 2x2 [Int] generation for the given 4x4 [Int] in its center.
 */
@Suppress("NOTHING_TO_INLINE")
internal inline fun Int.computeNextGeneration(): Int = f_Algorithm_exportComputeNextGen4x4UInt(this.toUInt()).toInt()

/**
 * Computes the 4x4 [Int] next generation for the given 8x8 64-bit Morton leaf node in its center.
 */
fun ULong.computeNextGeneration(): Int = f_Algorithm_exportComputeLeafNextGen8x8BranchUInt(this).toInt()

/**
 * Computes the 4x4 [Int] next generation for the given 8x8 64-bit Morton leaf node in its center.
 */
fun Long.computeNextGeneration(): Int = this.toULong().computeNextGeneration()

/**
 * Packs four 16-bit 4x4 quadrants in Morton order into an 8x8 64-bit leaf node.
 */
internal fun packLeafNode(nw: Int, ne: Int, sw: Int, se: Int): LeafNode = f_Algorithm_packLeafFrom4x4sUInt(
    nw.toUInt(),
    ne.toUInt(),
    sw.toUInt(),
    se.toUInt(),
)

/**
 * Extracts the central 4x4 from an 8x8 64-bit leaf node.
 */
internal fun centeredSubnodeLevel3(node: LeafNode): Int = f_Algorithm_centeredSubnodeLevel3BitsUInt(node).toInt()

/**
 * Extracts the horizontal central 4x4 spanning west and east 8x8 leaf nodes.
 */
internal fun centeredHorizontalSubnodeLevel3(w: LeafNode, e: LeafNode): Int =
    f_Algorithm_centeredHorizontalSubnodeLevel3BitsUInt(w, e).toInt()

/**
 * Extracts the vertical central 4x4 spanning north and south 8x8 leaf nodes.
 */
internal fun centeredVerticalSubnodeLevel3(n: LeafNode, s: LeafNode): Int =
    f_Algorithm_centeredVerticalSubnodeLevel3BitsUInt(n, s).toInt()

/**
 * Extracts the central 4x4 from a 16x16 Level 4 node consisting of four 8x8 leaf nodes.
 */
internal fun centeredSubSubnodeLevel4(nw: LeafNode, ne: LeafNode, sw: LeafNode, se: LeafNode): Int =
    f_Algorithm_centeredSubSubnodeLevel4BitsUInt(
        nw,
        ne,
        sw,
        se,
    ).toInt()

/**
 * Extracts the central 4x4 from a [MacroCell.Level4Node].
 */
internal fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
    centeredSubSubnodeLevel4(node.nw, node.ne, node.sw, node.se)

/**
 * Computes the next generation for a 16x16 Level 4 node, returning the centered 8x8 [LeafNode] leaf node.
 */
internal fun computeLevel4NextGeneration(nw: LeafNode, ne: LeafNode, sw: LeafNode, se: LeafNode): LeafNode =
    f_Algorithm_computeLevel4NextGen16x16UInt(
        nw,
        ne,
        sw,
        se,
    )

/**
 * Computes the next generation for a 16x16 Level 4 node, returning the centered 8x8 [LeafNode] leaf node,
 * delegating leaf computations to the provided [computeLeafNextGen] function.
 */
internal fun computeLevel4NextGeneration(
    nw: LeafNode,
    ne: LeafNode,
    sw: LeafNode,
    se: LeafNode,
    computeLeafNextGen: (LeafNode) -> Int,
): LeafNode = f_Algorithm_computeLevel4NextGen16x16WithUInt(
    nw = nw,
    ne = ne,
    sw = sw,
    se = se,
) { computeLeafNextGen(it).toUInt() }

/**
 * Computes the next generation for a [MacroCell.Level4Node], returning the centered 8x8 [LeafNode] leaf node.
 */
internal fun computeLevel4NextGeneration(node: MacroCell.Level4Node): LeafNode = computeLevel4NextGeneration(
    nw = node.nw,
    ne = node.ne,
    sw = node.sw,
    se = node.se,
)

/**
 * Computes the next generation for a [MacroCell.Level4Node], returning the centered 8x8 [LeafNode] leaf node,
 * delegating leaf computations to the provided [computeLeafNextGen] function.
 */
internal fun computeLevel4NextGeneration(node: MacroCell.Level4Node, computeLeafNextGen: (LeafNode) -> Int): LeafNode =
    f_Algorithm_stepLevel4NodeWith(node) { computeLeafNextGen(it).toUInt() }

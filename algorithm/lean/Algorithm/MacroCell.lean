/-
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
 -/

import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCellHash
import Lean.Compiler.Kotlin

open Lean.Compiler.Kotlin

local notation "ℕ" => Nat

namespace Algorithm

/--
A leaf MacroCell containing 64 cells encoded in a 64-bit word in Morton (Z-order) layout.
Matches MacroCell.LeafNode = Long in Kotlin.
-/
abbrev LeafNode := UInt64

/--
SWAR population count for 64-bit Morton leaf words.
Computes the exact number of active cells in O(1) bitwise operations.
-/
@[inline]
def popcount64 (x : UInt64) : UInt32 :=
  let m1 : UInt64 := 0x5555555555555555
  let m2 : UInt64 := 0x3333333333333333
  let m4 : UInt64 := 0x0F0F0F0F0F0F0F0F
  let h01 : UInt64 := 0x0101010101010101
  let x1 := x - ((x >>> 1) &&& m1)
  let x2 := (x1 &&& m2) + ((x1 >>> 2) &&& m2)
  let x3 := (x2 + (x2 >>> 4)) &&& m4
  let x4 := (x3 * h01) >>> 56
  x4.toUInt32

attribute [kotlin_expr "popcount64({0})"] popcount64

/--
Converts relative coordinates (0..7, 0..7) into a Morton bit index within an 8x8 leaf.
-/
@[export cell_to_leaf_bit]
def cellToLeafBitUInt (x y : UInt32) : UInt32 :=
  (x &&& (1 : UInt32)) |||
  ((y &&& (1 : UInt32)) <<< 1) |||
  ((x &&& (2 : UInt32)) <<< 1) |||
  ((y &&& (2 : UInt32)) <<< 2) |||
  ((x &&& (4 : UInt32)) <<< 2) |||
  ((y &&& (4 : UInt32)) <<< 3)

/--
Tests whether an 8x8 leaf has an active cell at relative coordinates (x, y).
-/
@[export leaf_contains]
def leafContains (leaf : UInt64) (x y : UInt32) : Bool :=
  let bit := cellToLeafBitUInt x y
  ((leaf >>> bit.toUInt64) &&& (1 : UInt64)) == 1

/--
Sets or clears an active cell in an 8x8 leaf at relative coordinates (x, y).
-/
@[export leaf_with_cell]
def leafWithCell (leaf : UInt64) (x y : UInt32) (isAlive : Bool) : UInt64 :=
  let bit := cellToLeafBitUInt x y
  let mask : UInt64 := (1 : UInt64) <<< bit.toUInt64
  if isAlive then
    leaf ||| mask
  else
    leaf &&& (~~~mask)

/--
A quadtree representation of the state of cells, matching Kotlin's `MacroCell`.
A `MacroCell` is either:
- A `Level4Node` with 4 64-bit `LeafNode` quadrants (16x16 cells).
- A `CellNode` with 4 subnodes of equal level >= 4 (representing 2^(k+1) x 2^(k+1) cells).
-/
@[kotlin_class "sealed class MacroCell"]
inductive MacroCell where
  | level4Node (hash : UInt32) (nw ne sw se : UInt64) : MacroCell
  | cellNode (hash : UInt32) (nw ne sw se : MacroCell) : MacroCell
deriving DecidableEq

/--
The tree level of this cell. A cell at level `k` represents 2^k x 2^k cells.
Minimum level is 4.
-/
@[export macrocell_level, noinline]
def MacroCell.level : MacroCell → UInt32
  | .level4Node _ _ _ _ _ => 4
  | .cellNode _ nw _ _ _ => nw.level + 1

attribute [kotlin_expr "macroCellLevel({0})"] MacroCell.level

/--
The memoized hashcode for MacroCell matching MacroCellHash.lean.
Level4Node uses Stafford's Mix13 hash on the 4 leaves.
CellNode uses MurmurHash3 fmix32 on level and the 4 child hashes.
-/
@[noinline]
def MacroCell.cellHashCode : MacroCell → UInt32
  | .level4Node h _ _ _ _ => h
  | .cellNode h _ _ _ _ => h

attribute [kotlin_expr "macroCellHashCode({0})"] MacroCell.cellHashCode

/--
Smart constructor for Level4Node that automatically computes the hash.
-/
@[export macrocell_make_level4_node]
def makeLevel4Node (nw ne sw se : UInt64) : MacroCell :=
  .level4Node (level4Hash nw ne sw se) nw ne sw se

/--
Smart constructor for CellNode that automatically computes the hash.
-/
@[export macrocell_make_cell_node]
def makeCellNode (nw ne sw se : MacroCell) : MacroCell :=
  .cellNode (cellNodeHash (nw.level + 1) nw.cellHashCode ne.cellHashCode sw.cellHashCode se.cellHashCode) nw ne sw se

/--
The number of alive cells represented by this MacroCell.
-/
@[export macrocell_size]
def MacroCell.size : MacroCell → UInt64
  | .level4Node _ nw ne sw se =>
    (popcount64 nw).toUInt64 + (popcount64 ne).toUInt64 + (popcount64 sw).toUInt64 + (popcount64 se).toUInt64
  | .cellNode _ nw ne sw se => nw.size + ne.size + sw.size + se.size

attribute [kotlin_expr "macroCellSize({0})"] MacroCell.size

/--
Structural equality predicate for MacroCell.
-/
@[export macrocell_equals]
def MacroCell.cellEquals (m : MacroCell) (other : MacroCell) : Bool :=
  match m, other with
  | .level4Node h1 nw1 ne1 sw1 se1, .level4Node h2 nw2 ne2 sw2 se2 =>
    h1 == h2 && nw1 == nw2 && ne1 == ne2 && sw1 == sw2 && se1 == se2
  | .cellNode h1 nw1 ne1 sw1 se1, .cellNode h2 nw2 ne2 sw2 se2 =>
    h1 == h2 && cellEquals nw1 nw2 && cellEquals ne1 ne2 && cellEquals sw1 sw2 && cellEquals se1 se2
  | _, _ => false

/--
Structural equality predicate for Level4Node.
-/
@[export macrocell_level4_node_equals]
def Level4Node.cellEquals (m : MacroCell) (other : MacroCell) : Bool :=
  match m, other with
  | .level4Node h1 nw1 ne1 sw1 se1, .level4Node h2 nw2 ne2 sw2 se2 =>
    h1 == h2 && nw1 == nw2 && ne1 == ne2 && sw1 == sw2 && se1 == se2
  | _, _ => false

/--
Structural equality predicate for CellNode.
-/
@[export macrocell_cell_node_equals]
def CellNode.cellEquals (m : MacroCell) (other : MacroCell) : Bool :=
  match m, other with
  | .cellNode h1 nw1 ne1 sw1 se1, .cellNode h2 nw2 ne2 sw2 se2 =>
    h1 == h2 && MacroCell.cellEquals nw1 nw2 && MacroCell.cellEquals ne1 ne2 &&
      MacroCell.cellEquals sw1 sw2 && MacroCell.cellEquals se1 se2
  | _, _ => false

/--
Kotlin hashCode member delegating to cellHashCode.
-/
@[export macrocell_hash_code]
def MacroCell.hashCode (m : MacroCell) : UInt32 :=
  m.cellHashCode

/--
An empty (all dead) level 4 MacroCell.
-/
def emptyLevel4 : MacroCell :=
  makeLevel4Node 0 0 0 0

attribute [kotlin_expr "emptyLevel4()"] emptyLevel4

/--
Creates an empty MacroCell at level k (k >= 4).
For levels <= 4, returns an empty level 4 node.
-/
def emptyNode : ℕ → MacroCell
  | 0 => emptyLevel4
  | 1 => emptyLevel4
  | 2 => emptyLevel4
  | 3 => emptyLevel4
  | 4 => emptyLevel4
  | k + 5 =>
    let sub := emptyNode (k + 4)
    makeCellNode sub sub sub sub

/--
Returns true if the MacroCell contains an alive cell at coordinates (x, y).
-/
@[export macrocell_contains]
def macroCellContains (m : MacroCell) (x y : Int32) : Bool :=
  let w : Int32 := (1 : Int32) <<< m.level.toInt32
  if x < 0 || y < 0 || x >= w || y >= w then false
  else
      let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
      let isNorth : Bool := y < half
      let isWest : Bool := x < half
      match m with
      | .level4Node _ nw ne sw se =>
        match isNorth, isWest with
        | true, true => leafContains nw x.toUInt32 y.toUInt32
        | true, false => leafContains ne (x - half).toUInt32 y.toUInt32
        | false, true => leafContains sw x.toUInt32 (y - half).toUInt32
        | false, false => leafContains se (x - half).toUInt32 (y - half).toUInt32
      | .cellNode _ nw ne sw se =>
        match isNorth, isWest with
        | true, true => macroCellContains nw x y
        | true, false => macroCellContains ne (x - half) y
        | false, true => macroCellContains sw x (y - half)
        | false, false => macroCellContains se (x - half) (y - half)

/--
Sets or clears the cell at coordinates (x, y) in the MacroCell.
-/
@[export macrocell_with_cell]
def macroCellWithCell (m : MacroCell) (x y : Int32) (isAlive : Bool) : MacroCell :=
  let w : Int32 := (1 : Int32) <<< m.level.toInt32
  if x < 0 || y < 0 || x >= w || y >= w then m
  else
    let half : Int32 := (1 : Int32) <<< (m.level.toInt32 - 1)
    let isNorth : Bool := y < half
    let isWest : Bool := x < half
    match m with
    | .level4Node _ nw ne sw se =>
      match isNorth, isWest with
      | true, true => makeLevel4Node (leafWithCell nw x.toUInt32 y.toUInt32 isAlive) ne sw se
      | true, false => makeLevel4Node nw (leafWithCell ne (x - half).toUInt32 y.toUInt32 isAlive) sw se
      | false, true => makeLevel4Node nw ne (leafWithCell sw x.toUInt32 (y - half).toUInt32 isAlive) se
      | false, false => makeLevel4Node nw ne sw (leafWithCell se (x - half).toUInt32 (y - half).toUInt32 isAlive)
    | .cellNode _ nw ne sw se =>
      match isNorth, isWest with
      | true, true => makeCellNode (macroCellWithCell nw x y isAlive) ne sw se
      | true, false => makeCellNode nw (macroCellWithCell ne (x - half) y isAlive) sw se
      | false, true => makeCellNode nw ne (macroCellWithCell sw x (y - half) isAlive) se
      | false, false => makeCellNode nw ne sw (macroCellWithCell se (x - half) (y - half) isAlive)

/--
A four-quadrant container for the intermediate results of HashLife step decomposition.
-/
@[kotlin_class "class StepQuadrants"]
structure StepQuadrants where
  nw : MacroCell
  ne : MacroCell
  sw : MacroCell
  se : MacroCell

/--
Result container for HashLife step preparation, pairing the offset delta with the prepared node.
-/
@[kotlin_class "class StepPreparation"]
structure StepPreparation where
  offsetDelta : Int32
  macroCell : MacroCell

/--
State container for HashLife stepping, tracking the (x, y) spatial offset and root MacroCell.
-/
@[kotlin_class "class HashLifeStepState"]
structure HashLifeStepState where
  offsetX : Int32
  offsetY : Int32
  macroCell : MacroCell

/--
Result container for generational cache pruning threshold calculation.
-/
@[kotlin_class "class PruneThresholds"]
structure PruneThresholds where
  oldestMacroToKeep : UInt64
  oldestLeafToKeep : UInt64

/--
Result container for multi-generation batch execution, containing the final HashLifeStepState
and the generational cache pruning thresholds.
-/
@[kotlin_class "class StepBatchResult"]
structure StepBatchResult where
  finalState : HashLifeStepState
  thresholds : PruneThresholds


/--
Extracts the center 8x8 leaf from a 16x16 Level 4 node.
In quadtree coordinates: nw = nw.se, ne = ne.sw, sw = sw.ne, se = se.nw.
-/
@[export macrocell_centered_subnode_level4, inline]
def centeredSubnodeLevel4 (nw ne sw se : UInt64) : UInt64 :=
  let nw_se := (nw >>> 48).toUInt32 &&& 0xFFFF
  let ne_sw := (ne >>> 32).toUInt32 &&& 0xFFFF
  let sw_ne := (sw >>> 16).toUInt32 &&& 0xFFFF
  let se_nw := se.toUInt32 &&& 0xFFFF
  (nw_se.toUInt64) |||
  (ne_sw.toUInt64 <<< 16) |||
  (sw_ne.toUInt64 <<< 32) |||
  (se_nw.toUInt64 <<< 48)

/--
Extracts the horizontal center 8x8 leaf spanning between west and east 16x16 nodes.
Matches centeredHorizontalSubnode(w, e) in Kotlin.
-/
@[export macrocell_centered_horizontal_subnode_level4, inline]
def centeredHorizontalSubnodeLevel4 (w_ne w_se e_nw e_sw : UInt64) : UInt64 :=
  centeredSubnodeLevel4 w_ne e_nw w_se e_sw

/--
Extracts the vertical center 8x8 leaf spanning between north and south 16x16 nodes.
Matches centeredVerticalSubnode(n, s) in Kotlin.
-/
@[export macrocell_centered_vertical_subnode_level4, inline]
def centeredVerticalSubnodeLevel4 (n_sw n_se s_nw s_ne : UInt64) : UInt64 :=
  centeredSubnodeLevel4 n_sw n_se s_nw s_ne

/--
Extracts the center subnode of level k-1 from a level k CellNode.
In quadtree coordinates, the center consists of:
  nw = nw.se, ne = ne.sw, sw = sw.ne, se = se.nw
-/
@[export macrocell_centered_subnode]
def centeredSubnode : MacroCell → MacroCell
  | .cellNode _ (.cellNode _ _ _ _ nw_se) (.cellNode _ _ _ ne_sw _)
              (.cellNode _ _ sw_ne _ _) (.cellNode _ se_nw _ _ _) =>
    makeCellNode nw_se ne_sw sw_ne se_nw
  | .cellNode _ (.level4Node _ _ _ _ nw_se) (.level4Node _ _ _ ne_sw _)
              (.level4Node _ _ sw_ne _ _) (.level4Node _ se_nw _ _ _) =>
    makeLevel4Node nw_se ne_sw sw_ne se_nw
  | .level4Node _ nw ne sw se =>
    makeLevel4Node 0 0 0 (centeredSubnodeLevel4 nw ne sw se)
  | m => m

/--
Extracts the horizontal center subnode spanning between west and east nodes.
-/
@[export macrocell_centered_horizontal_subnode]
def centeredHorizontalSubnode : MacroCell → MacroCell → MacroCell
  | .cellNode _ _ (.cellNode _ _ _ _ w_ne_se) _ (.cellNode _ _ w_se_ne _ _),
    .cellNode _ (.cellNode _ _ _ e_nw_sw _) _ (.cellNode _ e_sw_nw _ _ _) _ =>
    makeCellNode w_ne_se e_nw_sw w_se_ne e_sw_nw
  | .cellNode _ _ (.level4Node _ _ _ _ w_ne_se) _ (.level4Node _ _ w_se_ne _ _),
    .cellNode _ (.level4Node _ _ _ e_nw_sw _) _ (.level4Node _ e_sw_nw _ _ _) _ =>
    makeLevel4Node w_ne_se e_nw_sw w_se_ne e_sw_nw
  | .cellNode .., .cellNode .. => emptyLevel4
  | w, _ => w

/--
Extracts the vertical center subnode spanning between north and south nodes.
-/
@[export macrocell_centered_vertical_subnode]
def centeredVerticalSubnode : MacroCell → MacroCell → MacroCell
  | .cellNode _ _ _ (.cellNode _ _ _ _ n_sw_se) (.cellNode _ _ _ n_se_sw _),
    .cellNode _ (.cellNode _ _ s_nw_ne _ _) (.cellNode _ s_ne_nw _ _ _) _ _ =>
    makeCellNode n_sw_se n_se_sw s_nw_ne s_ne_nw
  | .cellNode _ _ _ (.level4Node _ _ _ _ n_sw_se) (.level4Node _ _ _ n_se_sw _),
    .cellNode _ (.level4Node _ _ s_nw_ne _ _) (.level4Node _ s_ne_nw _ _ _) _ _ =>
    makeLevel4Node n_sw_se n_se_sw s_nw_ne s_ne_nw
  | .cellNode .., .cellNode .. => emptyLevel4
  | n, _ => n

/--
Directly extracts the center sub-subnode without allocating intermediate nodes on the heap.
-/
@[export macrocell_centered_sub_subnode_fast]
def centeredSubSubnodeFast (m : MacroCell) : MacroCell :=
  match m with
  | .cellNode _ (.level4Node _ _ _ _ nw_se) (.level4Node _ _ _ ne_sw _)
                (.level4Node _ _ sw_ne _ _) (.level4Node _ se_nw _ _ _) =>
    makeLevel4Node 0 0 0 (centeredSubnodeLevel4 nw_se ne_sw sw_ne se_nw)
  | .cellNode _ (.cellNode _ _ _ _ (.cellNode _ _ _ _ a))
                (.cellNode _ _ _ (.cellNode _ _ _ b _) _)
                (.cellNode _ _ (.cellNode _ _ c _ _) _ _)
                (.cellNode _ (.cellNode _ d _ _ _) _ _ _) =>
    makeCellNode a b c d
  | .cellNode _ (.cellNode _ _ _ _ (.level4Node _ _ _ _ a))
                (.cellNode _ _ _ (.level4Node _ _ _ b _) _)
                (.cellNode _ _ (.level4Node _ _ c _ _) _ _)
                (.cellNode _ (.level4Node _ d _ _ _) _ _ _) =>
    makeLevel4Node a b c d
  | m => m

/--
Extracts the center sub-subnode from a node of level k >= 5.
-/
@[export macrocell_centered_sub_subnode]
def centeredSubSubnode (m : MacroCell) : MacroCell :=
  centeredSubnode (centeredSubnode m)

attribute [kotlin_expr "f_Algorithm_centeredSubSubnodeFast({0})"] centeredSubSubnode

/--
Direct scalar calculation of the population of the center sub-subnode without constructing any nodes.
-/
@[export macrocell_centered_sub_subnode_size_fast]
def centeredSubSubnodeSizeFast (m : MacroCell) : UInt64 :=
  match m with
  | .cellNode _ (.level4Node _ _ _ _ nw_se) (.level4Node _ _ _ ne_sw _)
                (.level4Node _ _ sw_ne _ _) (.level4Node _ se_nw _ _ _) =>
    (popcount64 (centeredSubnodeLevel4 nw_se ne_sw sw_ne se_nw)).toUInt64
  | .cellNode _ (.cellNode _ _ _ _ (.cellNode _ _ _ _ a))
                (.cellNode _ _ _ (.cellNode _ _ _ b _) _)
                (.cellNode _ _ (.cellNode _ _ c _ _) _ _)
                (.cellNode _ (.cellNode _ d _ _ _) _ _ _) =>
    a.size + b.size + c.size + d.size
  | .cellNode _ (.cellNode _ _ _ _ (.level4Node _ _ _ _ a))
                (.cellNode _ _ _ (.level4Node _ _ _ b _) _)
                (.cellNode _ _ (.level4Node _ _ c _ _) _ _)
                (.cellNode _ (.level4Node _ d _ _ _) _ _ _) =>
    (popcount64 a + popcount64 b + popcount64 c + popcount64 d).toUInt64
  | _ => 0

/--
Computes the population of the center sub-subnode.
-/
@[export macrocell_centered_sub_subnode_size]
def centeredSubSubnodeSize (m : MacroCell) : UInt64 :=
  (centeredSubSubnode m).size

attribute [kotlin_expr "f_Algorithm_centeredSubSubnodeSizeFast({0})"] centeredSubSubnodeSize

def emptySubnode : MacroCell → MacroCell
  | .level4Node .. => emptyLevel4
  | .cellNode _ nw _ _ _ =>
    let sub := emptySubnode nw
    makeCellNode sub sub sub sub

attribute [kotlin_expr "emptySubnode({0})"] emptySubnode

/--
Surrounds a MacroCell with empty nodes of matching size, creating a centered
macrocell of level k + 2.
-/
@[export macrocell_expand_centered]
def expandCentered : MacroCell → MacroCell
  | .level4Node _ nw ne sw se =>
    let e4 := emptyLevel4
    let nw_se := makeLevel4Node 0 0 0 nw
    let ne_sw := makeLevel4Node 0 0 ne 0
    let sw_ne := makeLevel4Node 0 sw 0 0
    let se_nw := makeLevel4Node se 0 0 0
    let q_nw := makeCellNode e4 e4 e4 nw_se
    let q_ne := makeCellNode e4 e4 ne_sw e4
    let q_sw := makeCellNode e4 sw_ne e4 e4
    let q_se := makeCellNode se_nw e4 e4 e4
    makeCellNode q_nw q_ne q_sw q_se
  | .cellNode _ nw ne sw se =>
    let ek := emptySubnode nw
    let nw_se := makeCellNode ek ek ek nw
    let ne_sw := makeCellNode ek ek ne ek
    let sw_ne := makeCellNode ek sw ek ek
    let se_nw := makeCellNode se ek ek ek
    let ek1 := makeCellNode ek ek ek ek
    let q_nw := makeCellNode ek1 ek1 ek1 nw_se
    let q_ne := makeCellNode ek1 ek1 ne_sw ek1
    let q_sw := makeCellNode ek1 sw_ne ek1 ek1
    let q_se := makeCellNode se_nw ek1 ek1 ek1
    makeCellNode q_nw q_ne q_sw q_se

/--
Offset delta in cells when expanding a MacroCell of the given level.
-/
@[export macrocell_expand_offset_delta, inline]
def expandOffsetDeltaUInt (level : UInt32) : Int32 :=
  -3 * ((1 : Int32) <<< (level.toInt32 - 1))

/--
Offset delta in cells when stepping a MacroCell of the given level without expansion.
-/
@[export macrocell_step_offset_delta, inline]
def stepOffsetDeltaUInt (level : UInt32) : Int32 :=
  (1 : Int32) <<< (level.toInt32 - 2)

/--
Determines if a MacroCell needs expansion before stepping.
-/
@[export macrocell_need_to_expand]
def needToExpand (m : MacroCell) : Bool :=
  m.level <= 4 || centeredSubSubnodeSize m != m.size

/--
Prepares a MacroCell for stepping by expanding if necessary and computing the cumulative offset delta.
-/
@[export macrocell_prepare_step]
def prepareStep (m : MacroCell) : StepPreparation :=
  if needToExpand m then
    let exp := expandCentered m
    { offsetDelta := expandOffsetDeltaUInt m.level + stepOffsetDeltaUInt exp.level
    , macroCell := exp }
  else
    { offsetDelta := stepOffsetDeltaUInt m.level
    , macroCell := m }

/--
Decomposes a CellNode into the 4 sub-quadrants of level k - 1 needed for HashLife recursive stepping.
-/
@[export macrocell_step_quadrants]
def stepQuadrants : MacroCell → StepQuadrants
  | .cellNode _ (.level4Node _ nw1 ne1 sw1 se1) (.level4Node _ nw2 ne2 sw2 se2)
                (.level4Node _ nw3 ne3 sw3 se3) (.level4Node _ nw4 ne4 sw4 se4) =>
    let n00 := centeredSubnodeLevel4 nw1 ne1 sw1 se1
    let n01 := centeredSubnodeLevel4 ne1 nw2 se1 sw2
    let n02 := centeredSubnodeLevel4 nw2 ne2 sw2 se2
    let n10 := centeredSubnodeLevel4 sw1 se1 nw3 ne3
    let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
    let n12 := centeredSubnodeLevel4 sw2 se2 nw4 ne4
    let n20 := centeredSubnodeLevel4 nw3 ne3 sw3 se3
    let n21 := centeredSubnodeLevel4 ne3 nw4 se3 sw4
    let n22 := centeredSubnodeLevel4 nw4 ne4 sw4 se4
    { nw := makeLevel4Node n00 n01 n10 n11
    , ne := makeLevel4Node n01 n02 n11 n12
    , sw := makeLevel4Node n10 n11 n20 n21
    , se := makeLevel4Node n11 n12 n21 n22 }
  | m@(.cellNode _ nw ne sw se) =>
    let n00 := centeredSubnode nw
    let n01 := centeredHorizontalSubnode nw ne
    let n02 := centeredSubnode ne
    let n10 := centeredVerticalSubnode nw sw
    let n11 := centeredSubSubnode m
    let n12 := centeredVerticalSubnode ne se
    let n20 := centeredSubnode sw
    let n21 := centeredHorizontalSubnode sw se
    let n22 := centeredSubnode se
    { nw := makeCellNode n00 n01 n10 n11
    , ne := makeCellNode n01 n02 n11 n12
    , sw := makeCellNode n10 n11 n20 n21
    , se := makeCellNode n11 n12 n21 n22 }
  | m => { nw := m, ne := m, sw := m, se := m }

/--
Stepping stepCellNodeWith on a CellNode:
If level == 5, steps each quadrant with stepLevel4 and returns a Level4Node.
If level > 5, steps each quadrant with stepCell and returns a CellNode.
-/
@[export macrocell_step_cell_node_with]
def stepCellNodeWith
    (m : MacroCell)
    (stepLevel4 : MacroCell → UInt64)
    (stepCell : MacroCell → MacroCell) : MacroCell :=
  match m with
  | .cellNode _ (.level4Node _ nw1 ne1 sw1 se1) (.level4Node _ nw2 ne2 sw2 se2)
                (.level4Node _ nw3 ne3 sw3 se3) (.level4Node _ nw4 ne4 sw4 se4) =>
    let n00 := centeredSubnodeLevel4 nw1 ne1 sw1 se1
    let n01 := centeredSubnodeLevel4 ne1 nw2 se1 sw2
    let n02 := centeredSubnodeLevel4 nw2 ne2 sw2 se2
    let n10 := centeredSubnodeLevel4 sw1 se1 nw3 ne3
    let n11 := centeredSubnodeLevel4 se1 sw2 ne3 nw4
    let n12 := centeredSubnodeLevel4 sw2 se2 nw4 ne4
    let n20 := centeredSubnodeLevel4 nw3 ne3 sw3 se3
    let n21 := centeredSubnodeLevel4 ne3 nw4 se3 sw4
    let n22 := centeredSubnodeLevel4 nw4 ne4 sw4 se4
    let q_nw := makeLevel4Node n00 n01 n10 n11
    let q_ne := makeLevel4Node n01 n02 n11 n12
    let q_sw := makeLevel4Node n10 n11 n20 n21
    let q_se := makeLevel4Node n11 n12 n21 n22
    makeLevel4Node (stepLevel4 q_nw) (stepLevel4 q_ne) (stepLevel4 q_sw) (stepLevel4 q_se)
  | m@(.cellNode _ nw ne sw se) =>
    let n00 := centeredSubnode nw
    let n01 := centeredHorizontalSubnode nw ne
    let n02 := centeredSubnode ne
    let n10 := centeredVerticalSubnode nw sw
    let n11 := centeredSubSubnode m
    let n12 := centeredVerticalSubnode ne se
    let n20 := centeredSubnode sw
    let n21 := centeredHorizontalSubnode sw se
    let n22 := centeredSubnode se
    let q_nw := makeCellNode n00 n01 n10 n11
    let q_ne := makeCellNode n01 n02 n11 n12
    let q_sw := makeCellNode n10 n11 n20 n21
    let q_se := makeCellNode n11 n12 n21 n22
    makeCellNode (stepCell q_nw) (stepCell q_ne) (stepCell q_sw) (stepCell q_se)
  | m =>
    makeCellNode (stepCell m) (stepCell m) (stepCell m) (stepCell m)


/--
Steps a HashLifeStepState by one generation, preparing the macrocell (expanding if necessary),
stepping the prepared node with `stepPrepared`, and updating spatial offsets.
-/
@[export hashlife_step_state_with]
def stepHashLifeStateWith
    (st : HashLifeStepState)
    (stepPrepared : MacroCell → MacroCell) : HashLifeStepState :=
  let prep := prepareStep st.macroCell
  let nextMacro := stepPrepared prep.macroCell
  { offsetX := st.offsetX + prep.offsetDelta
  , offsetY := st.offsetY + prep.offsetDelta
  , macroCell := nextMacro }

theorem uint32_sub_one_lt (n : UInt32) (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  cases n with
  | ofBitVec bv =>
    have hbv_ne : bv ≠ 0 := by
      intro hz
      apply h
      cases hz
      rfl
    have h1 : 1#32 ≤ bv := by bv_omega
    have h2 : 1 ≤ bv.toNat := by bv_omega
    have h3 : (bv - 1).toNat = bv.toNat - 1 := BitVec.toNat_sub_of_le h1
    change (bv - 1).toNat < bv.toNat
    omega

/--
Steps a HashLifeStepState by N generations using tail-recursive iteration.
-/
@[export hashlife_step_n_generations_with, kotlin_types "UInt" "Any?" "(Any?) -> Any?" "HashLifeStepState"]
def stepNGenerationsWith
    (step : UInt32)
    (st : HashLifeStepState)
    (stepOneGen : HashLifeStepState → HashLifeStepState) : HashLifeStepState :=
  if h : step = 0 then st
  else
    have : (step - 1).toNat < step.toNat := uint32_sub_one_lt step h
    stepNGenerationsWith (step - 1) (stepOneGen st) stepOneGen
termination_by step.toNat



/--
Calculates the oldest generation index to retain for macrocell caches and leaf caches.
-/
@[export hashlife_compute_prune_thresholds]
def computePruneThresholds
    (computedGenerations : UInt64)
    (generationsToCacheInMacroCellMaps : UInt32)
    (generationsToCacheInLeafNodeMap : UInt32) : PruneThresholds :=
  let macroKeep := generationsToCacheInMacroCellMaps.toUInt64
  let leafKeep := generationsToCacheInLeafNodeMap.toUInt64
  let oldestMacro := if computedGenerations >= macroKeep then computedGenerations - macroKeep else 0
  let oldestLeaf := if computedGenerations >= leafKeep then computedGenerations - leafKeep else 0
  { oldestMacroToKeep := oldestMacro, oldestLeafToKeep := oldestLeaf }

/--
Executes a multi-generation step batch and computes generational cache pruning thresholds.
-/
@[export hashlife_compute_generation_step]
def computeGenerationStep
    (step : UInt32)
    (st : HashLifeStepState)
    (computedGenerations : UInt64)
    (macroKeep leafKeep : UInt32)
    (stepOneGen : HashLifeStepState → HashLifeStepState) : StepBatchResult :=
  let finalSt := stepNGenerationsWith step st stepOneGen
  let thresh := computePruneThresholds (computedGenerations + step.toUInt64) macroKeep leafKeep
  { finalState := finalSt, thresholds := thresh }

/--
Computes the minimum MacroCell level (k >= 4) required to enclose a span of cells.
Uses bit-length calculation via UInt32.log2 without floating point operations.
-/
@[export macrocell_minimum_level]
def minimumMacroCellLevel (span : UInt32) : UInt32 :=
  if span ≤ 16 then 4
  else if (span - 1).log2 + 1 < 4 then 4
  else (span - 1).log2 + 1

/--
Dispatches canonicalization of a MacroCell:
- For Level4Node: delegates directly to `internLevel4`.
- For CellNode: checks `findExistingCell m` (fast path). If missing, recursively canonicalizes
  subnodes and interns the resulting node with `internCell`.
-/
@[export macrocell_canonicalize_with]
def canonicalizeMacroCellWith
    (m : MacroCell)
    (internLevel4 : MacroCell → MacroCell)
    (findExistingCell : MacroCell → Option MacroCell)
    (canonicalizeSubnode : MacroCell → MacroCell)
    (internCell : MacroCell → MacroCell) : MacroCell :=
  match m with
  | .level4Node .. => internLevel4 m
  | .cellNode _ nw ne sw se =>
    match findExistingCell m with
    | some existing => existing
    | none =>
      let withCanonicalSubNodes :=
        if m.size == 0 then
          let c := canonicalizeSubnode nw
          makeCellNode c c c c
        else
          makeCellNode
            (canonicalizeSubnode nw)
            (canonicalizeSubnode ne)
            (canonicalizeSubnode sw)
            (canonicalizeSubnode se)
      internCell withCanonicalSubNodes


@[inline]
def packCentralNibblesUInt (q0 q1 q2 q3 : UInt32) : UInt32 :=
  q0 ||| (q1 <<< 4) ||| (q2 <<< 8) ||| (q3 <<< 12)

@[export centeredSubnodeLevel3BitsUInt, inline]
def centeredSubnodeLevel3BitsUInt (leaf : UInt64) : UInt32 :=
  let nw := (leaf &&& (0xFFFF : UInt64)).toUInt32
  let ne := ((leaf >>> 16) &&& (0xFFFF : UInt64)).toUInt32
  let sw := ((leaf >>> 32) &&& (0xFFFF : UInt64)).toUInt32
  let se := ((leaf >>> 48) &&& (0xFFFF : UInt64)).toUInt32
  let q0 := (nw >>> 12) &&& (0xF : UInt32)
  let q1 := (ne >>> 8) &&& (0xF : UInt32)
  let q2 := (sw >>> 4) &&& (0xF : UInt32)
  let q3 := (se >>> 0) &&& (0xF : UInt32)
  packCentralNibblesUInt q0 q1 q2 q3

@[export centeredHorizontalSubnodeLevel3BitsUInt, inline]
def centeredHorizontalSubnodeLevel3BitsUInt (w e : UInt64) : UInt32 :=
  let w_ne := ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
  let w_se := ((w >>> 48) &&& (0xFFFF : UInt64)).toUInt32
  let e_nw := (e &&& (0xFFFF : UInt64)).toUInt32
  let e_sw := ((e >>> 32) &&& (0xFFFF : UInt64)).toUInt32
  let q0 := (w_ne >>> 12) &&& (0xF : UInt32)
  let q1 := (e_nw >>> 8) &&& (0xF : UInt32)
  let q2 := (w_se >>> 4) &&& (0xF : UInt32)
  let q3 := (e_sw >>> 0) &&& (0xF : UInt32)
  packCentralNibblesUInt q0 q1 q2 q3

@[export centeredVerticalSubnodeLevel3BitsUInt, inline]
def centeredVerticalSubnodeLevel3BitsUInt (n s : UInt64) : UInt32 :=
  let n_sw := ((n >>> 32) &&& (0xFFFF : UInt64)).toUInt32
  let n_se := ((n >>> 48) &&& (0xFFFF : UInt64)).toUInt32
  let s_nw := (s &&& (0xFFFF : UInt64)).toUInt32
  let s_ne := ((s >>> 16) &&& (0xFFFF : UInt64)).toUInt32
  let q0 := (n_sw >>> 12) &&& (0xF : UInt32)
  let q1 := (n_se >>> 8) &&& (0xF : UInt32)
  let q2 := (s_nw >>> 4) &&& (0xF : UInt32)
  let q3 := (s_ne >>> 0) &&& (0xF : UInt32)
  packCentralNibblesUInt q0 q1 q2 q3

@[export centeredSubSubnodeLevel4BitsUInt, inline]
def centeredSubSubnodeLevel4BitsUInt (nw ne sw se : UInt64) : UInt32 :=
  let nw_se := ((nw >>> 48) &&& (0xFFFF : UInt64)).toUInt32
  let ne_sw := ((ne >>> 32) &&& (0xFFFF : UInt64)).toUInt32
  let sw_ne := ((sw >>> 16) &&& (0xFFFF : UInt64)).toUInt32
  let se_nw := (se &&& (0xFFFF : UInt64)).toUInt32
  let q0 := (nw_se >>> 12) &&& (0xF : UInt32)
  let q1 := (ne_sw >>> 8) &&& (0xF : UInt32)
  let q2 := (sw_ne >>> 4) &&& (0xF : UInt32)
  let q3 := (se_nw >>> 0) &&& (0xF : UInt32)
  packCentralNibblesUInt q0 q1 q2 q3

@[export packLeafFrom4x4sUInt, inline]
def packLeafFrom4x4sUInt (q0 q1 q2 q3 : UInt32) : UInt64 :=
  (q0.toUInt64 &&& (0xFFFF : UInt64)) |||
  ((q1.toUInt64 &&& (0xFFFF : UInt64)) <<< 16) |||
  ((q2.toUInt64 &&& (0xFFFF : UInt64)) <<< 32) |||
  ((q3.toUInt64 &&& (0xFFFF : UInt64)) <<< 48)

@[export computeLevel4NextGen16x16WithUInt, specialize]
def computeLevel4NextGen16x16WithUInt
    (nw ne sw se : UInt64)
    (computeLeaf : UInt64 → UInt32) : UInt64 :=
  let n00 := centeredSubnodeLevel3BitsUInt nw
  let n01 := centeredHorizontalSubnodeLevel3BitsUInt nw ne
  let n02 := centeredSubnodeLevel3BitsUInt ne
  let n10 := centeredVerticalSubnodeLevel3BitsUInt nw sw
  let n11 := centeredSubSubnodeLevel4BitsUInt nw ne sw se
  let n12 := centeredVerticalSubnodeLevel3BitsUInt ne se
  let n20 := centeredSubnodeLevel3BitsUInt sw
  let n21 := centeredHorizontalSubnodeLevel3BitsUInt sw se
  let n22 := centeredSubnodeLevel3BitsUInt se

  let leafNW := packLeafFrom4x4sUInt n00 n01 n10 n11
  let leafNE := packLeafFrom4x4sUInt n01 n02 n11 n12
  let leafSW := packLeafFrom4x4sUInt n10 n11 n20 n21
  let leafSE := packLeafFrom4x4sUInt n11 n12 n21 n22

  let outNW := computeLeaf leafNW
  let outNE := computeLeaf leafNE
  let outSW := computeLeaf leafSW
  let outSE := computeLeaf leafSE

  packLeafFrom4x4sUInt outNW outNE outSW outSE

@[export computeLevel4NextGen16x16UInt]
def computeLevel4NextGen16x16UInt (nw ne sw se : UInt64) : UInt64 :=
  computeLevel4NextGen16x16WithUInt nw ne sw se computeLeafNextGen8x8BranchUInt

@[export macrocell_step_level4_node_with]
def stepLevel4NodeWith (m : MacroCell) (computeLeaf : UInt64 → UInt32) : UInt64 :=
  match m with
  | .level4Node _ nw ne sw se =>
    computeLevel4NextGen16x16WithUInt nw ne sw se computeLeaf
  | _ => 0

@[export hashlife_step_level4_node]
def stepLevel4Node (m : MacroCell) : UInt64 :=
  match m with
  | .level4Node _ nw ne sw se =>
    computeLevel4NextGen16x16UInt nw ne sw se
  | _ => 0

/--
The structural tree depth of this cell.
Minimum depth is 4 for Level4Node.
-/
def MacroCell.depth : MacroCell → ℕ
  | .level4Node .. => 4
  | .cellNode _ nw _ _ _ => nw.depth + 1

/--
Fuel-indexed recursive model of HashLife stepping over quadtree levels.
For level 4: steps to the central 8x8 leaf (placed in an empty level 4 node).
For level 5: steps four level-4 quadrants via `stepLevel4Node` to yield a level 4 node.
For level k > 5: steps four level-(k-1) quadrants recursively to yield a level-(k-1) node.
-/
def hashLifeStepRecursiveAux : ℕ → MacroCell → MacroCell
  | 0, _ => emptyLevel4
  | fuel + 1, m =>
    match m with
    | .level4Node _ nw ne sw se =>
      makeLevel4Node 0 0 0 (computeLevel4NextGen16x16UInt nw ne sw se)
    | .cellNode _ (.level4Node _ _ _ _ _) (.level4Node _ _ _ _ _)
                  (.level4Node _ _ _ _ _) (.level4Node _ _ _ _ _) =>
      let q := stepQuadrants m
      makeLevel4Node (stepLevel4Node q.nw) (stepLevel4Node q.ne) (stepLevel4Node q.sw) (stepLevel4Node q.se)
    | m@(.cellNode ..) =>
      let q := stepQuadrants m
      makeCellNode (hashLifeStepRecursiveAux fuel q.nw)
                   (hashLifeStepRecursiveAux fuel q.ne)
                   (hashLifeStepRecursiveAux fuel q.sw)
                   (hashLifeStepRecursiveAux fuel q.se)

def hashLifeStepRecursive (m : MacroCell) : MacroCell :=
  hashLifeStepRecursiveAux m.depth m

def hashLifeStep (m : MacroCell) : MacroCell :=
  hashLifeStepRecursive m

instance : Inhabited MacroCell := ⟨emptyLevel4⟩

def findLastLeafX (leaf : UInt64) (y : UInt32) : Option UInt32 :=
  if leafContains leaf 7 y then some 7
  else if leafContains leaf 6 y then some 6
  else if leafContains leaf 5 y then some 5
  else if leafContains leaf 4 y then some 4
  else if leafContains leaf 3 y then some 3
  else if leafContains leaf 2 y then some 2
  else if leafContains leaf 1 y then some 1
  else if leafContains leaf 0 y then some 0
  else none

def formatLeafRow (leaf : UInt64) (y : UInt32) : String :=
  match findLastLeafX leaf y with
  | none => ""
  | some lastX =>
    let rec loop (x : UInt32) (limit : UInt32) (acc : String) : String :=
      if h : x < limit then
        have : limit.toNat - (x + 1).toNat < limit.toNat - x.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (x + 1).toNat = x.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let ch := if leafContains leaf x y then '*' else '.'
        loop (x + 1) limit (acc.push ch)
      else acc
    termination_by limit.toNat - x.toNat
    loop 0 (lastX + 1) ""

def findLastLeafRow (leaf : UInt64) : Option UInt32 :=
  if (formatLeafRow leaf 7).length.toUInt32 != (0 : UInt32) then some 7
  else if (formatLeafRow leaf 6).length.toUInt32 != (0 : UInt32) then some 6
  else if (formatLeafRow leaf 5).length.toUInt32 != (0 : UInt32) then some 5
  else if (formatLeafRow leaf 4).length.toUInt32 != (0 : UInt32) then some 4
  else if (formatLeafRow leaf 3).length.toUInt32 != (0 : UInt32) then some 3
  else if (formatLeafRow leaf 2).length.toUInt32 != (0 : UInt32) then some 2
  else if (formatLeafRow leaf 1).length.toUInt32 != (0 : UInt32) then some 1
  else if (formatLeafRow leaf 0).length.toUInt32 != (0 : UInt32) then some 0
  else none

@[export macrocell_format_leaf]
def formatLeafNode (leaf : UInt64) : String :=
  match findLastLeafRow leaf with
  | none => "$"
  | some lastY =>
    let rec loop (y : UInt32) (limit : UInt32) (acc : String) : String :=
      if h : y < limit then
        have : limit.toNat - (y + 1).toNat < limit.toNat - y.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (y + 1).toNat = y.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let rowStr := formatLeafRow leaf y
        let nextAcc := if y == 0 then rowStr else acc ++ "$" ++ rowStr
        loop (y + 1) limit nextAcc
      else acc ++ "$"
    termination_by limit.toNat - y.toNat
    loop 0 (lastY + 1) ""

@[export macrocell_parse_leaf]
def parseLeafNode (s : String) : UInt64 :=
  let bytes := s.toByteArray
  let limit := bytes.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) (x y : UInt32) (acc : UInt64) : UInt64 :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let b := bytes.get! i.toNat
      if b == 36 then -- '$'
        loop (i + 1) limit 0 (y + 1) acc
      else if b == 42 then -- '*'
        let bit := cellToLeafBitUInt x y
        let mask : UInt64 := (1 : UInt64) <<< bit.toUInt64
        loop (i + 1) limit (x + 1) y (acc ||| mask)
      else -- '.' or other
        loop (i + 1) limit (x + 1) y acc
    else acc
  termination_by limit.toNat - i.toNat
  loop 0 limit 0 0 0

structure SerializerState where
  leafMap : Array (UInt64 × UInt32)
  cellMap : Array (MacroCell × UInt32)
  lines : Array String

def findLeafIndex (leaves : Array (UInt64 × UInt32)) (leaf : UInt64) : UInt32 :=
  let limit := leaves.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) : UInt32 :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (k, v) := leaves[i.toNat]!
      if k == leaf then v
      else loop (i + 1) limit
    else 0
  termination_by limit.toNat - i.toNat
  loop 0 limit

def findCellIndex (cells : Array (MacroCell × UInt32)) (cell : MacroCell) : UInt32 :=
  let limit := cells.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) : UInt32 :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (k, v) := cells[i.toNat]!
      if MacroCell.cellEquals k cell then v
      else loop (i + 1) limit
    else 0
  termination_by limit.toNat - i.toNat
  loop 0 limit

def visitLeaf (leaf : UInt64) (st : SerializerState) : UInt32 × SerializerState :=
  if leaf == 0 then (0, st)
  else
    let idx := findLeafIndex st.leafMap leaf
    if idx != 0 then (idx, st)
    else
      let newIdx := st.leafMap.size.toUInt32 + st.cellMap.size.toUInt32 + (1 : UInt32)
      let newLeafMap := st.leafMap.push (leaf, newIdx)
      let newLines := st.lines.push (formatLeafNode leaf)
      (newIdx, { st with leafMap := newLeafMap, lines := newLines })

def serializeTree (m : MacroCell) (st : SerializerState) : UInt32 × SerializerState :=
  if m.size == 0 then (0, st)
  else
    let idx := findCellIndex st.cellMap m
    if idx != 0 then (idx, st)
    else
      match m with
      | .level4Node _ nw ne sw se =>
        let (nwId, st1) := visitLeaf nw st
        let (neId, st2) := visitLeaf ne st1
        let (swId, st3) := visitLeaf sw st2
        let (seId, st4) := visitLeaf se st3
        let newIdx := st4.leafMap.size.toUInt32 + st4.cellMap.size.toUInt32 + (1 : UInt32)
        let newCellMap := st4.cellMap.push (m, newIdx)
        let line := s!"4 {nwId} {neId} {swId} {seId}"
        let newLines := st4.lines.push line
        (newIdx, { st4 with cellMap := newCellMap, lines := newLines })
      | .cellNode _ nw ne sw se =>
        let (nwId, st1) := serializeTree nw st
        let (neId, st2) := serializeTree ne st1
        let (swId, st3) := serializeTree sw st2
        let (seId, st4) := serializeTree se st3
        let newIdx := st4.leafMap.size.toUInt32 + st4.cellMap.size.toUInt32 + (1 : UInt32)
        let newCellMap := st4.cellMap.push (m, newIdx)
        let line := s!"{m.level} {nwId} {neId} {swId} {seId}"
        let newLines := st4.lines.push line
        (newIdx, { st4 with cellMap := newCellMap, lines := newLines })

@[export macrocell_serialize]
def serializeMacrocell (m : MacroCell) : Array String :=
  if m.size == 0 then
    #["[M2] (ComposeLife 1.0)"]
  else
    match m with
    | .level4Node _ nw ne sw se =>
      let nonZeroCount : UInt32 := (if nw != 0 then 1 else 0) +
                                   (if ne != 0 then 1 else 0) +
                                   (if sw != 0 then 1 else 0) +
                                   (if se != 0 then 1 else 0)
      if nonZeroCount == 1 then
        let leaf := if nw != 0 then nw else if ne != 0 then ne else if sw != 0 then sw else se
        #["[M2] (ComposeLife 1.0)", formatLeafNode leaf]
      else
        let initSt : SerializerState := {
          leafMap := #[],
          cellMap := #[],
          lines := #["[M2] (ComposeLife 1.0)"],
        }
        let (_, finalSt) := serializeTree m initSt
        finalSt.lines
    | _ =>
      let initSt : SerializerState := {
        leafMap := #[],
        cellMap := #[],
        lines := #["[M2] (ComposeLife 1.0)"],
      }
      let (_, finalSt) := serializeTree m initSt
      finalSt.lines

@[kotlin_class "MacrocellWarning"]
structure MacrocellWarning where
  tag : UInt32
  lineIndex : UInt32
  columnIndex : UInt32
  input : String
  deriving DecidableEq, Repr

@[kotlin_class "MacrocellResult"]
structure MacrocellResult where
  status : UInt32
  -- 0: Success
  -- 1: UnexpectedEmptyFile
  -- 2: UnexpectedHeader
  -- 3: UnexpectedInput
  -- 4: UnexpectedNodeId
  errLine : String
  errLineIndex : UInt32
  errColIndex : UInt32
  errRangeStart : UInt32
  errRangeEnd : UInt32
  warnings : Array MacrocellWarning
  macroCell : MacroCell
  deriving DecidableEq

@[inline]
def isDigitByteMC (b : UInt8) : Bool := b >= 48 && b <= 57

@[inline]
def isSpaceByteMC (b : UInt8) : Bool := b == 32 || b == 9 || b == 13

structure MCParseIntResult where
  val : UInt32
  nextPos : UInt32
  deriving DecidableEq, Repr

def parseUInt32AtMC (bytes : ByteArray) (pos limit : UInt32) : Option MCParseIntResult :=
  if pos >= limit then none
  else
    let rec loop (p : UInt32) (acc : UInt32) (hasDigits : Bool) : Option MCParseIntResult :=
      if h : p < limit then
        have : limit.toNat - (p + 1).toNat < limit.toNat - p.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (p + 1).toNat = p.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let b := bytes.get! p.toNat
        if isDigitByteMC b then
          loop (p + 1) (acc * 10 + (b.toUInt32 - 48)) true
        else if hasDigits then
          some ⟨acc, p⟩
        else
          none
      else if hasDigits then
        some ⟨acc, p⟩
      else
        none
    termination_by limit.toNat - p.toNat
    loop pos 0 false

def skipSpacesMC (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  if h : pos < limit then
    have : limit.toNat - (pos + 1).toNat < limit.toNat - pos.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    if isSpaceByteMC (bytes.get! pos.toNat) then
      skipSpacesMC bytes (pos + 1) limit
    else
      pos
  else
    pos
termination_by limit.toNat - pos.toNat

structure MCNodeLine where
  level : UInt32
  nw : UInt32
  nwStart : UInt32
  nwEnd : UInt32
  ne : UInt32
  neStart : UInt32
  neEnd : UInt32
  sw : UInt32
  swStart : UInt32
  swEnd : UInt32
  se : UInt32
  seStart : UInt32
  seEnd : UInt32
  deriving DecidableEq, Repr

def parseMCNodeLine (bytes : ByteArray) : Option MCNodeLine :=
  let limit := bytes.size.toUInt32
  let p0 := skipSpacesMC bytes 0 limit
  match parseUInt32AtMC bytes p0 limit with
  | none => none
  | some rLevel =>
    let p1 := skipSpacesMC bytes rLevel.nextPos limit
    match parseUInt32AtMC bytes p1 limit with
    | none => none
    | some rNW =>
      let p2 := skipSpacesMC bytes rNW.nextPos limit
      match parseUInt32AtMC bytes p2 limit with
      | none => none
      | some rNE =>
        let p3 := skipSpacesMC bytes rNE.nextPos limit
        match parseUInt32AtMC bytes p3 limit with
        | none => none
        | some rSW =>
          let p4 := skipSpacesMC bytes rSW.nextPos limit
          match parseUInt32AtMC bytes p4 limit with
          | none => none
          | some rSE =>
            let p5 := skipSpacesMC bytes rSE.nextPos limit
            if p5 == limit then
              some ⟨rLevel.val, rNW.val, p1, rNW.nextPos - 1, rNE.val, p2, rNE.nextPos - 1,
                    rSW.val, p3, rSW.nextPos - 1, rSE.val, p4, rSE.nextPos - 1⟩
            else none

instance : Inhabited MacroCell := ⟨emptyLevel4⟩

@[kotlin_class "MCFindLeafResult"]
structure MCFindLeafResult where
  found : Bool
  val : UInt64
  deriving Inhabited, DecidableEq

@[kotlin_class "MCFindCellResult"]
structure MCFindCellResult where
  found : Bool
  val : MacroCell
  deriving Inhabited, DecidableEq

def findLeafMC (leafIds : Array UInt32) (leafVals : Array UInt64) (id : UInt32) : MCFindLeafResult :=
  let limit := leafIds.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) : MCFindLeafResult :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      if leafIds[i.toNat]! == id then ⟨true, leafVals[i.toNat]!⟩
      else loop (i + 1) limit
    else ⟨false, 0⟩
  termination_by limit.toNat - i.toNat
  loop 0 limit

@[noinline]
def getCellAt (cellVals : Array MacroCell) (i : UInt32) : MacroCell :=
  let limit := cellVals.size.toUInt32
  if i < limit then
    match cellVals[i.toNat]! with
    | .level4Node _ nw ne sw se => makeLevel4Node nw ne sw se
    | other =>
      match other with
      | .cellNode _ nw ne sw se => makeCellNode nw ne sw se
      | _ => emptyLevel4
  else emptyLevel4

def findCellMC (cellIds : Array UInt32) (cellVals : Array MacroCell) (id : UInt32) : MCFindCellResult :=
  let limit := cellIds.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) : MCFindCellResult :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      if cellIds[i.toNat]! == id then ⟨true, getCellAt cellVals i⟩
      else loop (i + 1) limit
    else ⟨false, emptyLevel4⟩
  termination_by limit.toNat - i.toNat
  loop 0 limit

def emptyMacroCellUInt32 (level : UInt32) : MacroCell :=
  let rec loop (curLevel : UInt32) (curNode : MacroCell) : MacroCell :=
    if h : curLevel < level then
      have : level.toNat - (curLevel + 1).toNat < level.toNat - curLevel.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (curLevel + 1).toNat = curLevel.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt level
          simp only [UInt32.toNat_one]
          omega
        omega
      loop (curLevel + 1) (makeCellNode curNode curNode curNode curNode)
    else curNode
  termination_by level.toNat - curLevel.toNat
  if level <= 4 then emptyLevel4
  else loop 4 emptyLevel4

@[export macrocell_deserialize]
def deserializeMacrocell (lines : Array String) : MacrocellResult :=
  let numLines := lines.size.toUInt32
  if numLines == 0 then
    ⟨1, "", 0, 0, 0, 0, #[⟨0, 0, 0, ""⟩], emptyLevel4⟩
  else
    let headerLine := lines[0]!
    let hBytes := headerLine.toByteArray
    let hLimit := hBytes.size.toUInt32
    if hLimit < 4 || hBytes.get! 0 != 91 || hBytes.get! 1 != 77 || hBytes.get! 2 != 50 || hBytes.get! 3 != 93 then
      ⟨2, headerLine, 1, 0, 0, 0, #[], emptyLevel4⟩
    else
      let rec loopLines (i : UInt32) (numLines : UInt32) (nodeIdx : UInt32)
          (leafIds : Array UInt32) (leafVals : Array UInt64)
          (cellIds : Array UInt32) (cellVals : Array MacroCell)
          (warns : Array MacrocellWarning) : MacrocellResult :=
        if hl : i < numLines then
          have : numLines.toNat - (i + 1).toNat < numLines.toNat - i.toNat := by
            have h1 := UInt32.lt_iff_toNat_lt.mp hl
            have h2 : (i + 1).toNat = i.toNat + 1 := by
              rw [UInt32.toNat_add]
              have := UInt32.toNat_lt numLines
              simp only [UInt32.toNat_one]
              omega
            omega
          let line := lines[i.toNat]!
          let bytes := line.toByteArray
          let lineLen := bytes.size.toUInt32
          if lineLen == 0 then
            let newWarns := if i + 1 < numLines then warns.push ⟨1, i + 1, 0, ""⟩ else warns
            loopLines (i + 1) numLines nodeIdx leafIds leafVals cellIds cellVals newWarns
          else if bytes.get! 0 == 35 then -- '#'
            loopLines (i + 1) numLines nodeIdx leafIds leafVals cellIds cellVals warns
          else if isDigitByteMC (bytes.get! 0) then
            match parseMCNodeLine bytes with
            | none => ⟨3, line, i, 0, 0, 0, warns, emptyLevel4⟩
            | some nodeLine =>
              if nodeLine.level == 4 then
                let nwRes := if nodeLine.nw == 0 then ⟨true, 0⟩ else findLeafMC leafIds leafVals nodeLine.nw
                if !nwRes.found then ⟨4, line, i, 0, nodeLine.nwStart, nodeLine.nwEnd, warns, emptyLevel4⟩
                else
                  let neRes := if nodeLine.ne == 0 then ⟨true, 0⟩ else findLeafMC leafIds leafVals nodeLine.ne
                  if !neRes.found then ⟨4, line, i, 0, nodeLine.neStart, nodeLine.neEnd, warns, emptyLevel4⟩
                  else
                    let swRes := if nodeLine.sw == 0 then ⟨true, 0⟩ else findLeafMC leafIds leafVals nodeLine.sw
                    if !swRes.found then ⟨4, line, i, 0, nodeLine.swStart, nodeLine.swEnd, warns, emptyLevel4⟩
                    else
                      let seRes := if nodeLine.se == 0 then ⟨true, 0⟩ else findLeafMC leafIds leafVals nodeLine.se
                      if !seRes.found then ⟨4, line, i, 0, nodeLine.seStart, nodeLine.seEnd, warns, emptyLevel4⟩
                      else
                        let newNode := makeLevel4Node nwRes.val neRes.val swRes.val seRes.val
                        loopLines (i + 1) numLines (nodeIdx + 1) leafIds leafVals (cellIds.push nodeIdx) (cellVals.push newNode) warns
              else
                let emptySub := emptyMacroCellUInt32 (nodeLine.level - 1)
                let nwRes := if nodeLine.nw == 0 then ⟨true, emptySub⟩ else findCellMC cellIds cellVals nodeLine.nw
                if !nwRes.found then ⟨4, line, i, 0, nodeLine.nwStart, nodeLine.nwEnd, warns, emptyLevel4⟩
                else
                  let neRes := if nodeLine.ne == 0 then ⟨true, emptySub⟩ else findCellMC cellIds cellVals nodeLine.ne
                  if !neRes.found then ⟨4, line, i, 0, nodeLine.neStart, nodeLine.neEnd, warns, emptyLevel4⟩
                  else
                    let swRes := if nodeLine.sw == 0 then ⟨true, emptySub⟩ else findCellMC cellIds cellVals nodeLine.sw
                    if !swRes.found then ⟨4, line, i, 0, nodeLine.swStart, nodeLine.swEnd, warns, emptyLevel4⟩
                    else
                      let seRes := if nodeLine.se == 0 then ⟨true, emptySub⟩ else findCellMC cellIds cellVals nodeLine.se
                      if !seRes.found then ⟨4, line, i, 0, nodeLine.seStart, nodeLine.seEnd, warns, emptyLevel4⟩
                      else
                        let newNode := makeCellNode nwRes.val neRes.val swRes.val seRes.val
                        loopLines (i + 1) numLines (nodeIdx + 1) leafIds leafVals (cellIds.push nodeIdx) (cellVals.push newNode) warns
          else
            let rec checkLeafChars (col : UInt32) (limit : UInt32) (accWarns : Array MacrocellWarning) : Array MacrocellWarning :=
              if hc : col < limit then
                have : limit.toNat - (col + 1).toNat < limit.toNat - col.toNat := by
                  have h1 := UInt32.lt_iff_toNat_lt.mp hc
                  have h2 : (col + 1).toNat = col.toNat + 1 := by
                    rw [UInt32.toNat_add]
                    have := UInt32.toNat_lt limit
                    simp only [UInt32.toNat_one]
                    omega
                  omega
                let b := bytes.get! col.toNat
                let newAcc :=
                  if b != 36 && b != 46 && b != 42 then -- not in '$', '.', '*'
                    accWarns.push ⟨2, i, col, line⟩
                  else accWarns
                checkLeafChars (col + 1) limit newAcc
              else accWarns
            termination_by limit.toNat - col.toNat
            let leafWarns := checkLeafChars 0 lineLen warns
            let leafVal := parseLeafNode line
            loopLines (i + 1) numLines (nodeIdx + 1) (leafIds.push nodeIdx) (leafVals.push leafVal) cellIds cellVals leafWarns
        else
          if nodeIdx == 1 then
            ⟨0, "", 0, 0, 0, 0, warns, emptyLevel4⟩
          else
            let rootRes := findCellMC cellIds cellVals (nodeIdx - 1)
            if rootRes.found then
              ⟨0, "", 0, 0, 0, 0, warns, rootRes.val⟩
            else
              let leafRes := findLeafMC leafIds leafVals (nodeIdx - 1)
              if leafRes.found then
                ⟨0, "", 0, 0, 0, 0, warns, makeLevel4Node leafRes.val 0 0 0⟩
              else
                ⟨3, "", 0, 0, 0, 0, warns, emptyLevel4⟩
      termination_by numLines.toNat - i.toNat
      loopLines 1 numLines 1 #[] #[] #[] #[] #[]

def generateEmptyNodesKotlin : String := Id.run do
  let mut lines := #[]
  lines := lines.push "val EMPTY_LEVEL_4: MacroCell.Level4Node = MacroCell.Level4Node(0uL, 0uL, 0uL, 0uL)"
  for l in [5:33] do
    let node := emptyNode l
    match node with
    | .cellNode h _ _ _ _ =>
      let prev := if l == 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{l-1}"
      lines := lines.push s!"private val emptyNode_{l}: MacroCell.CellNode = MacroCell.CellNode({h}u, {prev}, {prev}, {prev}, {prev})"
    | _ => pure ()

  let mut arrElems := #[]
  for _ in [:5] do
    arrElems := arrElems.push "EMPTY_LEVEL_4"
  for l in [5:33] do
    arrElems := arrElems.push s!"emptyNode_{l}"

  lines := lines.push s!"val EMPTY_NODES: Array<MacroCell> = arrayOf(\n    {String.intercalate ",\n    " arrElems.toList},\n)"
  String.intercalate "\n\n" lines.toList

@[kotlin_file]
def macroCellFileSpec : FileSpec := {
  imports := #[
    "import com.alexvanyo.composelife.algorithm.computeNextGen4x4"
  ]
  items := #[
    .cls {
      name := "MacroCell"
      header := "sealed class MacroCell"
      body := #[
        .members,
        .verbatim "abstract val hash: UInt
abstract fun level(): UInt
abstract fun size(): ULong
fun centeredSubSubnodeSize(): ULong = f_Algorithm_centeredSubSubnodeSizeFast(this)
fun cellHashCode(): UInt = hash
override fun hashCode(): Int = hash.toInt()

class Level4Node(
    override val hash: UInt,
    val nw: ULong,
    val ne: ULong,
    val sw: ULong,
    val se: ULong,
) : MacroCell() {
    companion object {
        operator fun invoke(nw: ULong, ne: ULong, sw: ULong, se: ULong): Level4Node =
            f_Algorithm_makeLevel4Node(nw, ne, sw, se) as Level4Node
    }

    override fun level(): UInt = 4u

    private val _size: ULong =
        nw.countOneBits().toULong() +
            ne.countOneBits().toULong() +
            sw.countOneBits().toULong() +
            se.countOneBits().toULong()

    override fun size(): ULong = _size

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is Level4Node) return false
        if (hash != other.hash) return false
        if (nw == other.nw && ne == other.ne && sw == other.sw && se == other.se) return true
        return f_Algorithm_Level4Node_cellEquals(this, other)
    }
}

class CellNode(
    override val hash: UInt,
    val nw: MacroCell,
    val ne: MacroCell,
    val sw: MacroCell,
    val se: MacroCell,
) : MacroCell() {
    companion object {
        operator fun invoke(nw: MacroCell, ne: MacroCell, sw: MacroCell, se: MacroCell): CellNode =
            f_Algorithm_makeCellNode(nw, ne, sw, se) as CellNode
    }

    init {
        require(nw.level() == ne.level())
        require(ne.level() == sw.level())
        require(sw.level() == se.level())
    }

    private val _level: UInt = nw.level() + 1u

    override fun level(): UInt = _level

    private val _size: ULong = nw.size() + ne.size() + sw.size() + se.size()

    override fun size(): ULong = _size

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is CellNode) return false
        if (hash != other.hash) return false
        if (level() != other.level()) return false
        if (nw === other.nw && ne === other.ne && sw === other.sw && se === other.se) return true
        return f_Algorithm_CellNode_cellEquals(this, other)
    }
}"
      ]
    },
    .verbatim generateEmptyNodesKotlin,
    .topLevel
  ]
}

end Algorithm


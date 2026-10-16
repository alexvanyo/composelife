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
import Algorithm.Cache
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

attribute [kotlin_expr "{0}.countOneBits().toUInt()"] popcount64

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
@[export macrocell_level]
def MacroCell.level : MacroCell → UInt32
  | .level4Node _ _ _ _ _ => 4
  | .cellNode _ nw _ _ _ => nw.level + 1

attribute [kotlin_expr "{0}.level()"] MacroCell.level

/--
The memoized hashcode for MacroCell matching MacroCellHash.lean.
Level4Node uses Stafford's Mix13 hash on the 4 leaves.
CellNode uses MurmurHash3 fmix32 on level and the 4 child hashes.
-/
def MacroCell.cellHashCode : MacroCell → UInt32
  | .level4Node h _ _ _ _ => h
  | .cellNode h _ _ _ _ => h

attribute [kotlin_expr "{0}.hash"] MacroCell.cellHashCode

/--
Smart constructor for Level4Node that automatically computes the hash.
-/
def makeLevel4Node (nw ne sw se : UInt64) : MacroCell :=
  .level4Node (level4Hash nw ne sw se) nw ne sw se

/--
Smart constructor for CellNode that automatically computes the hash.
-/
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

attribute [kotlin_expr "{0}.size()"] MacroCell.size

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
  | .cellNode _ _ w_ne _ w_se, .cellNode _ e_nw _ e_sw _ =>
    match w_ne, w_se, e_nw, e_sw with
    | .cellNode _ _ _ _ w_ne_se, .cellNode _ _ w_se_ne _ _,
      .cellNode _ _ _ e_nw_sw _, .cellNode _ e_sw_nw _ _ _ =>
      makeCellNode w_ne_se e_nw_sw w_se_ne e_sw_nw
    | .level4Node _ _ _ _ w_ne_se, .level4Node _ _ w_se_ne _ _,
      .level4Node _ _ _ e_nw_sw _, .level4Node _ e_sw_nw _ _ _ =>
      makeLevel4Node w_ne_se e_nw_sw w_se_ne e_sw_nw
    | _, _, _, _ => emptyLevel4
  | w, _ => w

/--
Extracts the vertical center subnode spanning between north and south nodes.
-/
@[export macrocell_centered_vertical_subnode]
def centeredVerticalSubnode : MacroCell → MacroCell → MacroCell
  | .cellNode _ _ _ n_sw n_se, .cellNode _ s_nw s_ne _ _ =>
    match n_sw, n_se, s_nw, s_ne with
    | .cellNode _ _ _ _ n_sw_se, .cellNode _ _ _ n_se_sw _,
      .cellNode _ _ s_nw_ne _ _, .cellNode _ s_ne_nw _ _ _ =>
      makeCellNode n_sw_se n_se_sw s_nw_ne s_ne_nw
    | .level4Node _ _ _ _ n_sw_se, .level4Node _ _ _ n_se_sw _,
      .level4Node _ _ s_nw_ne _ _, .level4Node _ s_ne_nw _ _ _ =>
      makeLevel4Node n_sw_se n_se_sw s_nw_ne s_ne_nw
    | _, _, _, _ => emptyLevel4
  | n, _ => n

/--
Extracts the center sub-subnode from a node of level k >= 5.
-/
@[export macrocell_centered_sub_subnode]
def centeredSubSubnode (m : MacroCell) : MacroCell :=
  centeredSubnode (centeredSubnode m)

/--
Computes the population of the center sub-subnode.
-/
@[export macrocell_centered_sub_subnode_size]
def centeredSubSubnodeSize (m : MacroCell) : UInt64 :=
  (centeredSubSubnode m).size

attribute [kotlin_expr "{0}.centeredSubSubnodeSize()"] centeredSubSubnodeSize

def emptySubnode : MacroCell → MacroCell
  | .level4Node .. => emptyLevel4
  | .cellNode _ nw _ _ _ =>
    let sub := emptySubnode nw
    makeCellNode sub sub sub sub

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

/--
Determines equivalence between two CellNodes with already-canonical subnodes based on hash and pointer equivalence.
-/
@[export macrocell_canonical_cell_node_equals]
def canonicalCellNodeEquals (a b : MacroCell) : Bool :=
  match a, b with
  | .cellNode _ nw1 ne1 sw1 se1, .cellNode _ nw2 ne2 sw2 se2 =>
    a.level == b.level &&
    nw1.cellHashCode == nw2.cellHashCode && ne1.cellHashCode == ne2.cellHashCode &&
    sw1.cellHashCode == sw2.cellHashCode && se1.cellHashCode == se2.cellHashCode
  | _, _ => false


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

@[export computeLevel4NextGen16x16WithUInt]
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

/--
Suite of 5 caches mirroring HashLifeAlgorithm.kt:
- canonicalLevel4Map
- canonicalCellNodeMap
- cellNodeMap
- level4NodeMap
- leafNodeMap
-/
structure HashLifeCaches where
  canonicalLevel4Map : Cache MacroCell MacroCell
  canonicalCellNodeMap : Cache MacroCell MacroCell
  cellNodeMap : Cache MacroCell MacroCell
  level4NodeMap : ObjectLongCache MacroCell
  leafNodeMap : LongIntCache
  computedGenerations : UInt64
deriving DecidableEq

/--
Initializes an empty HashLife cache suite.
-/
def initHashLifeCaches : HashLifeCaches :=
  { canonicalLevel4Map := Cache.empty
  , canonicalCellNodeMap := Cache.empty
  , cellNodeMap := Cache.empty
  , level4NodeMap := Cache.empty
  , leafNodeMap := Cache.empty
  , computedGenerations := 0 }

/--
Prunes all caches to the specified generational thresholds.
-/
def pruneHashLifeCaches (caches : HashLifeCaches) (macroKeep leafKeep : UInt64) : HashLifeCaches :=
  let oldestMacro := if caches.computedGenerations >= macroKeep then caches.computedGenerations - macroKeep else 0
  let oldestLeaf := if caches.computedGenerations >= leafKeep then caches.computedGenerations - leafKeep else 0
  { canonicalLevel4Map := caches.canonicalLevel4Map.prune oldestMacro
  , canonicalCellNodeMap := caches.canonicalCellNodeMap.prune oldestMacro
  , cellNodeMap := caches.cellNodeMap.prune oldestMacro
  , level4NodeMap := caches.level4NodeMap.prune oldestMacro
  , leafNodeMap := caches.leafNodeMap.prune oldestLeaf
  , computedGenerations := caches.computedGenerations }

/--
Canonicalizes a CellNode by canonicalizing its subnodes with `canonicalize`.
If size is 0, only canonicalizes nw once.
-/
@[export macrocell_make_canonical_cell_node_with]
def makeCanonicalCellNodeWith (m : MacroCell) (canonicalize : MacroCell → MacroCell) : MacroCell :=
  match m with
  | .cellNode _ nw ne sw se =>
    if m.size == 0 then
      let c := canonicalize nw
      makeCellNode c c c c
    else
      makeCellNode (canonicalize nw) (canonicalize ne) (canonicalize sw) (canonicalize se)
  | _ => m

/--
Canonicalizes a MacroCell using the canonical caches (hash-consing).
-/
def makeCanonical (m : MacroCell) (caches : HashLifeCaches) : MacroCell × HashLifeCaches :=
  match m with
  | .level4Node .. =>
    let (canon, newL4Map) := caches.canonicalLevel4Map.get id m caches.computedGenerations
    (canon, { caches with canonicalLevel4Map := newL4Map })
  | .cellNode _ nw ne sw se =>
    let (cnw, c1) := makeCanonical nw caches
    let (cne, c2) := makeCanonical ne c1
    let (csw, c3) := makeCanonical sw c2
    let (cse, c4) := makeCanonical se c3
    let canonicalForm := makeCellNode cnw cne csw cse
    let (canon, newCellMap) := c4.canonicalCellNodeMap.get id canonicalForm c4.computedGenerations
    (canon, { c4 with canonicalCellNodeMap := newCellMap })

/--
Cached next generation computation using `cellNodeMap` and `level4NodeMap`.
-/
def cachedComputeNextGen (m : MacroCell) (caches : HashLifeCaches) : MacroCell × HashLifeCaches :=
  let (canon, c1) := makeCanonical m caches
  let (res, newStepMap) := c1.cellNodeMap.get hashLifeStep canon c1.computedGenerations
  (res, { c1 with cellNodeMap := newStepMap, computedGenerations := c1.computedGenerations + 1 })

@[kotlin_file]
def macroCellFileSpec : FileSpec := {
  imports := #[]
  items := #[
    .cls {
      name := "MacroCell"
      header := "sealed class MacroCell"
      body := #[
        .members,
        .verbatim "abstract val hash: UInt
abstract fun level(): UInt
abstract fun size(): ULong
abstract fun centeredSubSubnodeSize(): ULong
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

    override fun centeredSubSubnodeSize(): ULong = 0uL

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

    override fun centeredSubSubnodeSize(): ULong {
        val nw = nw
        val ne = ne
        val sw = sw
        val se = se
        return when (nw) {
            is Level4Node -> {
                ne as Level4Node
                sw as Level4Node
                se as Level4Node
                f_Algorithm_centeredSubnodeLevel4(nw.se, ne.sw, sw.ne, se.nw).countOneBits().toULong()
            }
            is CellNode -> {
                ne as CellNode
                sw as CellNode
                se as CellNode
                val c0 = nw.se
                val c1 = ne.sw
                val c2 = sw.ne
                val c3 = se.nw
                when (c0) {
                    is CellNode -> {
                        (c0 as CellNode).se.size() +
                            (c1 as CellNode).sw.size() +
                            (c2 as CellNode).ne.size() +
                            (c3 as CellNode).nw.size()
                    }
                    is Level4Node -> {
                        (c0 as Level4Node).se.countOneBits().toULong() +
                            (c1 as Level4Node).sw.countOneBits().toULong() +
                            (c2 as Level4Node).ne.countOneBits().toULong() +
                            (c3 as Level4Node).nw.countOneBits().toULong()
                    }
                }
            }
        }
    }

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
    .topLevel
  ]
}

end Algorithm


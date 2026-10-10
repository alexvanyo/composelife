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
import Algorithm.MacroCell
import AlgorithmDefs
import proofs.MacroCellProofs

local notation "ℕ" => Nat

namespace Algorithm

/--
Population count of an all-zero 64-bit leaf is 0.
-/
theorem popcount64_zero : popcount64 0 = 0 :=
  popcount64_zero_Impl

/--
Extracting the center 8x8 leaf from four empty leaves produces an empty leaf.
-/
theorem centeredSubnodeLevel4_zero : centeredSubnodeLevel4 0 0 0 0 = 0 :=
  centeredSubnodeLevel4_zero_Impl

/--
Level 4 nodes have level 4.
-/
theorem macroCell_level_level4Node (hash : UInt32) (nw ne sw se : UInt64) :
    (MacroCell.level4Node hash nw ne sw se).level = 4 :=
  macroCell_level_level4Node_Impl hash nw ne sw se

/--
Cell nodes have level equal to child level + 1.
-/
theorem macroCell_level_cellNode (hash : UInt32) (nw ne sw se : MacroCell) :
    (MacroCell.cellNode hash nw ne sw se).level = nw.level + 1 :=
  macroCell_level_cellNode_Impl hash nw ne sw se

/--
An empty level 4 node has size 0.
-/
theorem macroCell_size_emptyLevel4 : emptyLevel4.size = 0 :=
  macroCell_size_emptyLevel4_Impl

/--
Empty nodes at any level have size 0.
-/
theorem macroCell_size_emptyNode (k : ℕ) : (emptyNode k).size = 0 :=
  macroCell_size_emptyNode_Impl k

/--
Empty nodes at any level are well-formed.
-/
theorem macroCell_emptyNode_isWellFormed (k : ℕ) : isWellFormed (emptyNode k) :=
  macroCell_emptyNode_isWellFormed_Impl k

/--
Horizontal reflection on MacroCell is an involution.
-/
theorem macroCell_flipX_involution (m : MacroCell) :
    macroCellFlipX (macroCellFlipX m) = m :=
  macroCell_flipX_involution_Impl m

/--
Vertical reflection on MacroCell is an involution.
-/
theorem macroCell_flipY_involution (m : MacroCell) :
    macroCellFlipY (macroCellFlipY m) = m :=
  macroCell_flipY_involution_Impl m

/--
Structural equality on MacroCell is reflexive.
-/
theorem macroCell_cellEquals_refl (m : MacroCell) :
    m.cellEquals m = true :=
  macroCell_cellEquals_refl_Impl m

/--
Structural equality on MacroCell is equivalent to propositional equality.
-/
theorem macroCell_cellEquals_iff_eq (m1 m2 : MacroCell) :
    m1.cellEquals m2 = true ↔ m1 = m2 :=
  macroCell_cellEquals_iff_eq_Impl m1 m2

/--
Kotlin hashCode matches cellHashCode.
-/
theorem macroCell_hashCode_eq (m : MacroCell) :
    m.hashCode = m.cellHashCode :=
  macroCell_hashCode_eq_Impl m

/--
Extracting the horizontal center 8x8 leaf from four empty leaves produces an empty leaf.
-/
theorem centeredHorizontalSubnodeLevel4_zero :
    centeredHorizontalSubnodeLevel4 0 0 0 0 = 0 :=
  centeredHorizontalSubnodeLevel4_zero_Impl

/--
Extracting the vertical center 8x8 leaf from four empty leaves produces an empty leaf.
-/
theorem centeredVerticalSubnodeLevel4_zero :
    centeredVerticalSubnodeLevel4 0 0 0 0 = 0 :=
  centeredVerticalSubnodeLevel4_zero_Impl

/--
The population of the central sub-subnode of an empty level 4 node is 0.
-/
theorem centeredSubSubnodeSize_emptyLevel4 :
    centeredSubSubnodeSize emptyLevel4 = 0 :=
  centeredSubSubnodeSize_emptyLevel4_Impl

/--
Expanding a level 4 node shifts the bounding box offset by -24 cells.
-/
theorem expandOffsetDeltaUInt_four :
    expandOffsetDeltaUInt 4 = -24 :=
  expandOffsetDeltaUInt_four_Impl

/--
Stepping a level 4 node shifts the center offset by 4 cells.
-/
theorem stepOffsetDeltaUInt_four :
    stepOffsetDeltaUInt 4 = 4 :=
  stepOffsetDeltaUInt_four_Impl

/--
An empty level 4 node requires expansion before stepping.
-/
theorem needToExpand_emptyLevel4 :
    needToExpand emptyLevel4 = true :=
  needToExpand_emptyLevel4_Impl

/--
Decomposing an empty level 4 node produces four empty level 4 nodes.
-/
theorem stepQuadrants_emptyLevel4 :
    stepQuadrants emptyLevel4 = { nw := emptyLevel4, ne := emptyLevel4, sw := emptyLevel4, se := emptyLevel4 } :=
  stepQuadrants_emptyLevel4_Impl

/--
Stepping a Level4Node with stepCellNodeWith delegates to stepCell.
-/
theorem stepCellNodeWith_level4Node
    (hash : UInt32) (nw ne sw se : UInt64)
    (stepLevel4 : MacroCell → UInt64)
    (stepCell : MacroCell → MacroCell) :
    stepCellNodeWith (.level4Node hash nw ne sw se) stepLevel4 stepCell =
      makeCellNode (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se)) :=
  stepCellNodeWith_level4Node_Impl hash nw ne sw se stepLevel4 stepCell

/--
Canonicalizing a non-CellNode with makeCanonicalCellNodeWith returns the node unchanged.
-/
theorem makeCanonicalCellNodeWith_level4Node
    (hash : UInt32) (nw ne sw se : UInt64)
    (canonicalize : MacroCell → MacroCell) :
    makeCanonicalCellNodeWith (.level4Node hash nw ne sw se) canonicalize =
      .level4Node hash nw ne sw se :=
  makeCanonicalCellNodeWith_level4Node_Impl hash nw ne sw se canonicalize

/--
When a MacroCell does not need expansion, prepareStep leaves the node unchanged and returns stepOffsetDeltaUInt.
-/
theorem prepareStep_needToExpand_false (m : MacroCell) (h : needToExpand m = false) :
    (prepareStep m).macroCell = m ∧ (prepareStep m).offsetDelta = stepOffsetDeltaUInt m.level :=
  prepareStep_needToExpand_false_Impl m h

/--
Morton coordinate encoding of (0, 0) is bit index 0.
-/
theorem cellToLeafBitUInt_zero : cellToLeafBitUInt 0 0 = 0 :=
  cellToLeafBitUInt_zero_Impl

/--
An all-zero leaf contains no active cells at (0, 0).
-/
theorem leafContains_zero_zero : leafContains 0 0 0 = false :=
  leafContains_zero_zero_Impl

/--
An empty level 4 MacroCell contains no active cells at (0, 0).
-/
theorem macroCellContains_emptyLevel4_zero_zero :
    macroCellContains emptyLevel4 0 0 = false :=
  macroCellContains_emptyLevel4_zero_zero_Impl

/--
Setting cell at negative coordinates outside bounds leaves the MacroCell unchanged.
-/
theorem macroCellWithCell_neg : macroCellWithCell emptyLevel4 (-1) 0 false = emptyLevel4 :=
  macroCellWithCell_neg_Impl

end Algorithm

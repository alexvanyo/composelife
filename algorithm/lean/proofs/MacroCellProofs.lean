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

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

theorem popcount64_zero_Impl :
    popcount64 0 = 0 := by
  rfl

theorem centeredSubnodeLevel4_zero_Impl :
    centeredSubnodeLevel4 0 0 0 0 = 0 := by
  rfl

theorem macroCell_level_level4Node_Impl (hash : UInt32) (nw ne sw se : UInt64) :
    (MacroCell.level4Node hash nw ne sw se).level = 4 := by
  rfl

theorem macroCell_level_cellNode_Impl (hash : UInt32) (nw ne sw se : MacroCell) :
    (MacroCell.cellNode hash nw ne sw se).level = nw.level + 1 := by
  rfl

theorem macroCell_size_emptyLevel4_Impl :
    emptyLevel4.size = 0 := by
  rfl

theorem macroCell_size_emptyNode_Impl : ∀ (k : ℕ),
    (emptyNode k).size = 0
  | 0 => by rfl
  | 1 => by rfl
  | 2 => by rfl
  | 3 => by rfl
  | 4 => by rfl
  | k + 5 => by
    dsimp [emptyNode, makeCellNode, MacroCell.size]
    have ih := macroCell_size_emptyNode_Impl (k + 4)
    rw [ih]
    rfl

theorem macroCell_emptyNode_isWellFormed_Impl : ∀ (k : ℕ),
    isWellFormed (emptyNode k)
  | 0 => by trivial
  | 1 => by trivial
  | 2 => by trivial
  | 3 => by trivial
  | 4 => by trivial
  | k + 5 => by
    dsimp [emptyNode, makeCellNode, isWellFormed, MacroCell.level]
    have ih := macroCell_emptyNode_isWellFormed_Impl (k + 4)
    exact ⟨ih, ih, ih, ih, rfl, rfl, rfl⟩

theorem macroCell_flipX_involution_Impl : ∀ (m : MacroCell),
    macroCellFlipX (macroCellFlipX m) = m
  | .level4Node h nw ne sw se => by rfl
  | .cellNode h nw ne sw se => by
    dsimp [macroCellFlipX]
    rw [macroCell_flipX_involution_Impl nw,
        macroCell_flipX_involution_Impl ne,
        macroCell_flipX_involution_Impl sw,
        macroCell_flipX_involution_Impl se]

theorem macroCell_flipY_involution_Impl : ∀ (m : MacroCell),
    macroCellFlipY (macroCellFlipY m) = m
  | .level4Node h nw ne sw se => by rfl
  | .cellNode h nw ne sw se => by
    dsimp [macroCellFlipY]
    rw [macroCell_flipY_involution_Impl nw,
        macroCell_flipY_involution_Impl ne,
        macroCell_flipY_involution_Impl sw,
        macroCell_flipY_involution_Impl se]

theorem macroCell_cellEquals_refl_Impl (m : MacroCell) :
    m.cellEquals m = true := by
  induction m with
  | level4Node h nw ne sw se =>
    simp [MacroCell.cellEquals]
  | cellNode h nw ne sw se ih_nw ih_ne ih_sw ih_se =>
    simp [MacroCell.cellEquals, ih_nw, ih_ne, ih_sw, ih_se]

theorem macroCell_cellEquals_iff_eq_Impl (m1 m2 : MacroCell) :
    m1.cellEquals m2 = true ↔ m1 = m2 := by
  induction m1 generalizing m2 with
  | level4Node h1 nw1 ne1 sw1 se1 =>
    cases m2 with
    | level4Node h2 nw2 ne2 sw2 se2 =>
      simp [MacroCell.cellEquals, and_assoc]
    | cellNode h2 nw2 ne2 sw2 se2 =>
      simp [MacroCell.cellEquals]
  | cellNode h1 nw1 ne1 sw1 se1 ih_nw ih_ne ih_sw ih_se =>
    cases m2 with
    | level4Node h2 nw2 ne2 sw2 se2 =>
      simp [MacroCell.cellEquals]
    | cellNode h2 nw2 ne2 sw2 se2 =>
      simp [MacroCell.cellEquals, ih_nw, ih_ne, ih_sw, ih_se, and_assoc]

theorem macroCell_hashCode_eq_Impl (m : MacroCell) :
    m.hashCode = m.cellHashCode := by
  rfl

theorem centeredHorizontalSubnodeLevel4_zero_Impl :
    centeredHorizontalSubnodeLevel4 0 0 0 0 = 0 := by
  rfl

theorem centeredVerticalSubnodeLevel4_zero_Impl :
    centeredVerticalSubnodeLevel4 0 0 0 0 = 0 := by
  rfl

theorem centeredSubSubnodeSize_emptyLevel4_Impl :
    centeredSubSubnodeSize emptyLevel4 = 0 := by
  rfl

theorem expandOffsetDeltaUInt_four_Impl :
    expandOffsetDeltaUInt 4 = -24 := by
  rfl

theorem stepOffsetDeltaUInt_four_Impl :
    stepOffsetDeltaUInt 4 = 4 := by
  rfl

theorem needToExpand_emptyLevel4_Impl :
    needToExpand emptyLevel4 = true := by
  rfl

theorem stepQuadrants_emptyLevel4_Impl :
    stepQuadrants emptyLevel4 = { nw := emptyLevel4, ne := emptyLevel4, sw := emptyLevel4, se := emptyLevel4 } := by
  rfl

theorem stepCellNodeWith_level4Node_Impl
    (hash : UInt32) (nw ne sw se : UInt64)
    (stepLevel4 : MacroCell → UInt64)
    (stepCell : MacroCell → MacroCell) :
    stepCellNodeWith (.level4Node hash nw ne sw se) stepLevel4 stepCell =
      makeCellNode (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se))
                   (stepCell (.level4Node hash nw ne sw se)) := by
  rfl

theorem makeCanonicalCellNodeWith_level4Node_Impl
    (hash : UInt32) (nw ne sw se : UInt64)
    (canonicalize : MacroCell → MacroCell) :
    makeCanonicalCellNodeWith (.level4Node hash nw ne sw se) canonicalize =
      .level4Node hash nw ne sw se := by
  rfl

theorem prepareStep_needToExpand_false_Impl (m : MacroCell) (h : needToExpand m = false) :
    (prepareStep m).macroCell = m ∧ (prepareStep m).offsetDelta = stepOffsetDeltaUInt m.level := by
  dsimp [prepareStep]
  simp [h]

theorem cellToLeafBitUInt_zero_Impl : cellToLeafBitUInt 0 0 = 0 := by
  rfl

theorem leafContains_zero_zero_Impl : leafContains 0 0 0 = false := by
  decide

theorem macroCellContains_emptyLevel4_zero_zero_Impl :
    macroCellContains emptyLevel4 0 0 = false := by
  decide

theorem macroCellWithCell_neg_Impl : macroCellWithCell emptyLevel4 (-1) 0 false = emptyLevel4 := by
  decide

end Algorithm

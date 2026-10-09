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

theorem macroCell_level_level4Node_Impl (nw ne sw se : UInt64) :
    (MacroCell.level4Node nw ne sw se).level = 4 := by
  rfl

theorem macroCell_level_cellNode_Impl (nw ne sw se : MacroCell) :
    (MacroCell.cellNode nw ne sw se).level = nw.level + 1 := by
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
    dsimp [emptyNode, MacroCell.size]
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
    dsimp [emptyNode, isWellFormed]
    have ih := macroCell_emptyNode_isWellFormed_Impl (k + 4)
    exact ⟨ih, ih, ih, ih, rfl, rfl, rfl⟩

theorem macroCell_flipX_involution_Impl : ∀ (m : MacroCell),
    macroCellFlipX (macroCellFlipX m) = m
  | .level4Node nw ne sw se => by rfl
  | .cellNode nw ne sw se => by
    dsimp [macroCellFlipX]
    rw [macroCell_flipX_involution_Impl nw,
        macroCell_flipX_involution_Impl ne,
        macroCell_flipX_involution_Impl sw,
        macroCell_flipX_involution_Impl se]

theorem macroCell_flipY_involution_Impl : ∀ (m : MacroCell),
    macroCellFlipY (macroCellFlipY m) = m
  | .level4Node nw ne sw se => by rfl
  | .cellNode nw ne sw se => by
    dsimp [macroCellFlipY]
    rw [macroCell_flipY_involution_Impl nw,
        macroCell_flipY_involution_Impl ne,
        macroCell_flipY_involution_Impl sw,
        macroCell_flipY_involution_Impl se]

end Algorithm

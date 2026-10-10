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
import Algorithm.HashLife
import Algorithm.HashLifeEquivalence
import AlgorithmDefs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Layer 4: 9-Subnode Geometric Decomposition & Quadrant Tiling
-- =========================================================================

theorem subnodes_quadrants_level (sn : HashLifeSubnodes)
    (h_level : sn.n00.level = sn.n01.level ∧
               sn.n01.level = sn.n02.level ∧
               sn.n02.level = sn.n10.level ∧
               sn.n10.level = sn.n11.level ∧
               sn.n11.level = sn.n12.level ∧
               sn.n12.level = sn.n20.level ∧
               sn.n20.level = sn.n21.level ∧
               sn.n21.level = sn.n22.level) :
    (quadrantNW sn).level = sn.n11.level + 1 ∧
    (quadrantNE sn).level = sn.n11.level + 1 ∧
    (quadrantSW sn).level = sn.n11.level + 1 ∧
    (quadrantSE sn).level = sn.n11.level + 1 := by
  dsimp [quadrantNW, quadrantNE, quadrantSW, quadrantSE, makeCellNode, MacroCell.level]
  rcases h_level with ⟨h01, h12, h23, h34, _h45, _h56, _h67, _h78⟩
  have heq0 : sn.n00.level = sn.n11.level := by rw [h01, h12, h23, h34]
  have heq1 : sn.n01.level = sn.n11.level := by rw [h12, h23, h34]
  have heq2 : sn.n10.level = sn.n11.level := by rw [h34]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq0]
  · rw [heq1]
  · rw [heq2]
  · rfl

theorem stepQuadrants_level5_quadrant_levels
    (nw1 ne1 sw1 se1 nw2 ne2 sw2 se2 nw3 ne3 sw3 se3 nw4 ne4 sw4 se4 : UInt64) :
    let m := makeCellNode
      (makeLevel4Node nw1 ne1 sw1 se1)
      (makeLevel4Node nw2 ne2 sw2 se2)
      (makeLevel4Node nw3 ne3 sw3 se3)
      (makeLevel4Node nw4 ne4 sw4 se4)
    let q := stepQuadrants m
    q.nw.level = 4 ∧ q.ne.level = 4 ∧ q.sw.level = 4 ∧ q.se.level = 4 := by
  intro m q
  dsimp [m, q, stepQuadrants, makeLevel4Node]
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem stepQuadrants_offset_alignment (k : ℕ) (hk : k >= 5) :
    stepOffsetDelta k + stepOffsetDelta (k - 1) =
    (2 : ℤ) ^ (k - 2) + (2 : ℤ) ^ (k - 3) := by
  dsimp [stepOffsetDelta]
  have h1 : k - 1 - 2 = k - 3 := by omega
  rw [h1]

theorem quadrant_grid_decomposition (ox oy : ℤ) (nw ne sw se : MacroCell) :
    let m := makeCellNode nw ne sw se
    macroCellToGrid ox oy m =
      macroCellToGrid ox oy nw ++
      macroCellToGrid (ox + (2 : ℤ) ^ nw.level.toNat) oy ne ++
      macroCellToGrid ox (oy + (2 : ℤ) ^ nw.level.toNat) sw ++
      macroCellToGrid (ox + (2 : ℤ) ^ nw.level.toNat) (oy + (2 : ℤ) ^ nw.level.toNat) se := by
  intro m
  rfl

end Algorithm

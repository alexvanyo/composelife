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
import AlgorithmDefs

local notation "ℕ" => Nat

namespace Algorithm

theorem bit_comp_empty_correct_Impl :
    verifyBitComputation4x4 0 = true := by
  decide

theorem bit_comp_blinker_h_correct_Impl :
    verifyBitComputation4x4 (2^3 + 2^6 + 2^7) = true := by
  decide

theorem bit_comp_blinker_v_correct_Impl :
    verifyBitComputation4x4 (2^1 + 2^3 + 2^9) = true := by
  decide

theorem bit_comp_block_correct_Impl :
    verifyBitComputation4x4 (2^3 + 2^6 + 2^9 + 2^12) = true := by
  decide

theorem bit_comp_glider_sub_correct_Impl :
    verifyBitComputation4x4 (2^1 + 2^6 + 2^8 + 2^9 + 2^12) = true := by
  decide

theorem bit_comp_tub_correct_Impl :
    verifyBitComputation4x4 (2^1 + 2^2 + 2^6 + 2^9) = true := by
  decide

theorem leaf_comp_empty_correct_Impl :
    verifyLeafComputation8x8 0 = true := by
  decide

theorem leaf_comp_centered_block_correct_Impl :
    verifyLeafComputation8x8 (2^0x0F + 2^0x1A + 2^0x25 + 2^0x30) = true := by
  decide

theorem leaf_comp_centered_blinker_h_correct_Impl :
    verifyLeafComputation8x8 (2^0x0E + 2^0x0F + 2^0x1A) = true := by
  decide

theorem leaf_comp_centered_tub_correct_Impl :
    verifyLeafComputation8x8 (2^0x0D + 2^0x0E + 2^0x1A + 2^0x25) = true := by
  decide

theorem bitRule_equals_lifeRule_Impl (alive : Bool) (n : ℕ) :
    bitRule n alive = lifeRule alive n := by
  cases alive <;> rfl

theorem mask11_is_exact_moore_neighborhood_Impl :
    mask11Neighbors.all (mooreNeighbors (1, 1)).contains ∧
    (mooreNeighbors (1, 1)).all mask11Neighbors.contains ∧
    mask11Neighbors.length = 8 := by
  decide

theorem mask21_is_exact_moore_neighborhood_Impl :
    mask21Neighbors.all (mooreNeighbors (2, 1)).contains ∧
    (mooreNeighbors (2, 1)).all mask21Neighbors.contains ∧
    mask21Neighbors.length = 8 := by
  decide

theorem mask12_is_exact_moore_neighborhood_Impl :
    mask12Neighbors.all (mooreNeighbors (1, 2)).contains ∧
    (mooreNeighbors (1, 2)).all mask12Neighbors.contains ∧
    mask12Neighbors.length = 8 := by
  decide

theorem mask22_is_exact_moore_neighborhood_Impl :
    mask22Neighbors.all (mooreNeighbors (2, 2)).contains ∧
    (mooreNeighbors (2, 2)).all mask22Neighbors.contains ∧
    mask22Neighbors.length = 8 := by
  decide

theorem nw_quadrant_contains_all_moore_neighbors_Impl :
    let centerNW : List Coord := [(2, 2), (3, 2), (2, 3), (3, 3)]
    centerNW.all (fun c => (mooreNeighbors c).all nwQuadrantCoords.contains) = true := by
  decide

theorem ne_quadrant_contains_all_moore_neighbors_Impl :
    let centerNE : List Coord := [(4, 2), (5, 2), (4, 3), (5, 3)]
    centerNE.all (fun c => (mooreNeighbors c).all neQuadrantCoords.contains) = true := by
  decide

theorem sw_quadrant_contains_all_moore_neighbors_Impl :
    let centerSW : List Coord := [(2, 4), (3, 4), (2, 5), (3, 5)]
    centerSW.all (fun c => (mooreNeighbors c).all swQuadrantCoords.contains) = true := by
  decide

theorem se_quadrant_contains_all_moore_neighbors_Impl :
    let centerSE : List Coord := [(4, 4), (5, 4), (4, 5), (5, 5)]
    centerSE.all (fun c => (mooreNeighbors c).all seQuadrantCoords.contains) = true := by
  decide

theorem computeLeafNextGen8x8Fast_eq_computeLeafNextGen8x8_Impl (w : ℕ) :
    computeLeafNextGen8x8Fast w = computeLeafNextGen8x8 w := by
  rfl

theorem computeLeafNextGen8x8Fast_zero_Impl :
    computeLeafNextGen8x8Fast 0 = 0 := by
  rfl

theorem computeLeafNextGen8x8Branch_eq_computeLeafNextGen8x8_Impl (w : ℕ) :
    computeLeafNextGen8x8Branch w = computeLeafNextGen8x8 w := by
  unfold computeLeafNextGen8x8Branch
  split
  · rename_i h
    have heq : w = 0 := of_decide_eq_true h
    rw [heq]
    rfl
  · exact computeLeafNextGen8x8Fast_eq_computeLeafNextGen8x8_Impl w

end Algorithm

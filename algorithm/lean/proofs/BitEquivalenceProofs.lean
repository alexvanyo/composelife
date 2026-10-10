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
import AlgorithmDefs
import proofs.BitComputationProofs
import theorems.BitComputationTheorems

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Layer 1: Bitwise Base Equivalence (4x4 -> 2x2)
-- =========================================================================

theorem testBit_nibble (b0 b1 b2 b3 : Bool) :
    let n := boolToNat b3 * 8 + boolToNat b2 * 4 + boolToNat b1 * 2 + boolToNat b0
    (testBit n 0 = b0) ∧
    (testBit n 1 = b1) ∧
    (testBit n 2 = b2) ∧
    (testBit n 3 = b3) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

theorem bit11_alive_iff (w : ℕ) :
    testBit (computeNextGen4x4 w) 0 = bitRule (neighborCount11 w) (testBit w 3) := by
  dsimp [computeNextGen4x4]
  have h := (testBit_nibble
    (bitRule (neighborCount11 w) (testBit w 3))
    (bitRule (neighborCount21 w) (testBit w 6))
    (bitRule (neighborCount12 w) (testBit w 9))
    (bitRule (neighborCount22 w) (testBit w 12))).1
  exact h

theorem bit21_alive_iff (w : ℕ) :
    testBit (computeNextGen4x4 w) 1 = bitRule (neighborCount21 w) (testBit w 6) := by
  dsimp [computeNextGen4x4]
  have h := (testBit_nibble
    (bitRule (neighborCount11 w) (testBit w 3))
    (bitRule (neighborCount21 w) (testBit w 6))
    (bitRule (neighborCount12 w) (testBit w 9))
    (bitRule (neighborCount22 w) (testBit w 12))).2.1
  exact h

theorem bit12_alive_iff (w : ℕ) :
    testBit (computeNextGen4x4 w) 2 = bitRule (neighborCount12 w) (testBit w 9) := by
  dsimp [computeNextGen4x4]
  have h := (testBit_nibble
    (bitRule (neighborCount11 w) (testBit w 3))
    (bitRule (neighborCount21 w) (testBit w 6))
    (bitRule (neighborCount12 w) (testBit w 9))
    (bitRule (neighborCount22 w) (testBit w 12))).2.2.1
  exact h

theorem bit22_alive_iff (w : ℕ) :
    testBit (computeNextGen4x4 w) 3 = bitRule (neighborCount22 w) (testBit w 12) := by
  dsimp [computeNextGen4x4]
  have h := (testBit_nibble
    (bitRule (neighborCount11 w) (testBit w 3))
    (bitRule (neighborCount21 w) (testBit w 6))
    (bitRule (neighborCount12 w) (testBit w 9))
    (bitRule (neighborCount22 w) (testBit w 12))).2.2.2
  exact h

theorem bit_rule_moore_agreement (w : ℕ) :
    (testBit (computeNextGen4x4 w) 0 = lifeRule (testBit w 3) (neighborCount11 w)) ∧
    (testBit (computeNextGen4x4 w) 1 = lifeRule (testBit w 6) (neighborCount21 w)) ∧
    (testBit (computeNextGen4x4 w) 2 = lifeRule (testBit w 9) (neighborCount12 w)) ∧
    (testBit (computeNextGen4x4 w) 3 = lifeRule (testBit w 12) (neighborCount22 w)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bit11_alive_iff, bitRule_equals_lifeRule]
  · rw [bit21_alive_iff, bitRule_equals_lifeRule]
  · rw [bit12_alive_iff, bitRule_equals_lifeRule]
  · rw [bit22_alive_iff, bitRule_equals_lifeRule]

theorem centerBitsToCoords_contains_iff (out : ℕ) (c : Coord) :
    c ∈ centerBitsToCoords out ↔
    (c = (1, 1) ∧ testBit out 0 = true) ∨
    (c = (2, 1) ∧ testBit out 1 = true) ∨
    (c = (1, 2) ∧ testBit out 2 = true) ∨
    (c = (2, 2) ∧ testBit out 3 = true) := by
  dsimp [centerBitsToCoords]
  cases h0 : testBit out 0 <;>
  cases h1 : testBit out 1 <;>
  cases h2 : testBit out 2 <;>
  cases h3 : testBit out 3 <;>
  simp

-- =========================================================================
-- Universal 4x4 Bit Computation Correctness on Representative Configurations
-- =========================================================================

theorem bit_comp_empty_Impl :
    verifyBitComputation4x4 0 = true :=
  bit_comp_empty_correct_Impl

theorem bit_comp_block_Impl :
    verifyBitComputation4x4 (2^3 + 2^6 + 2^9 + 2^12) = true :=
  bit_comp_block_correct_Impl

theorem bit_comp_blinker_h_Impl :
    verifyBitComputation4x4 (2^3 + 2^6 + 2^7) = true :=
  bit_comp_blinker_h_correct_Impl

theorem bit_comp_blinker_v_Impl :
    verifyBitComputation4x4 (2^1 + 2^3 + 2^9) = true :=
  bit_comp_blinker_v_correct_Impl

theorem bit_comp_tub_Impl :
    verifyBitComputation4x4 (2^1 + 2^2 + 2^6 + 2^9) = true :=
  bit_comp_tub_correct_Impl

theorem bit_comp_glider_Impl :
    verifyBitComputation4x4 (2^1 + 2^6 + 2^8 + 2^9 + 2^12) = true :=
  bit_comp_glider_sub_correct_Impl

-- =========================================================================
-- Layer 2: 8x8 Leaf and 16x16 Level 4 Stepping Equivalence
-- =========================================================================

theorem leaf_comp_empty_Impl :
    verifyLeafComputation8x8 0 = true :=
  leaf_comp_empty_correct_Impl

theorem leaf_comp_branch_eq (w : ℕ) :
    computeLeafNextGen8x8Branch w = computeLeafNextGen8x8 w :=
  computeLeafNextGen8x8Branch_eq_computeLeafNextGen8x8 w

theorem computeLevel4_zero_leaves :
    computeLevel4NextGen16x16 0 0 0 0 = 0 := by
  dsimp [computeLevel4NextGen16x16, centeredSubnodeLevel3Bits,
         centeredHorizontalSubnodeLevel3Bits, centeredVerticalSubnodeLevel3Bits,
         centeredSubSubnodeLevel4Bits, packCentralNibbles, packLeafFrom4x4s]
  rfl

theorem computeLevel4NextGen16x16UInt_zero_eq :
    computeLevel4NextGen16x16UInt 0 0 0 0 = 0 := by
  decide

end Algorithm

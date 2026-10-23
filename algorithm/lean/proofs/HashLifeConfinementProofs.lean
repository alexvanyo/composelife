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
import proofs.SemanticModelProofs
import proofs.HashLifeKernelProofs
import proofs.HashLifeStepProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Population Counts
-- =========================================================================

theorem macroCellSize_level4Node (h : UInt32) (nw ne sw se : UInt64) :
    macroCellSize (.level4Node h nw ne sw se) =
    (popcount64 nw).toNat + (popcount64 ne).toNat + (popcount64 sw).toNat + (popcount64 se).toNat := by
  have h1 := popcount64_toNat_le nw
  have h2 := popcount64_toNat_le ne
  have h3 := popcount64_toNat_le sw
  have h4 := popcount64_toNat_le se
  simp only [macroCellSize, UInt32.toNat_add]
  omega

theorem macroCellSize_cellNode (h : UInt32) (nw ne sw se : MacroCell) :
    macroCellSize (.cellNode h nw ne sw se) =
    macroCellSize nw + macroCellSize ne + macroCellSize sw + macroCellSize se := rfl

theorem size_toNat : ∀ (m : MacroCell), m.size.toNat = macroCellSize m % 2 ^ 64
  | .level4Node h nw ne sw se => by
    rw [macroCellSize_level4Node]
    have h1 := popcount64_toNat_le nw
    have h2 := popcount64_toNat_le ne
    have h3 := popcount64_toNat_le sw
    have h4 := popcount64_toNat_le se
    simp only [MacroCell.size, UInt64.toNat_add, UInt32.toNat_toUInt64]
    omega
  | .cellNode h nw ne sw se => by
    rw [macroCellSize_cellNode]
    simp only [MacroCell.size, UInt64.toNat_add, size_toNat nw, size_toNat ne, size_toNat sw,
      size_toNat se]
    omega

/-- A node of depth `d` holds at most `4^d` alive cells. -/
theorem macroCellSize_le_pow : ∀ {m : MacroCell} {d : ℕ}, WFd m d → macroCellSize m ≤ 4 ^ d
  | .level4Node _ nw ne sw se, d, h => by
    rw [WFd_level4Node_iff] at h
    subst h
    rw [macroCellSize_level4Node]
    have h1 := popcount64_toNat_le nw
    have h2 := popcount64_toNat_le ne
    have h3 := popcount64_toNat_le sw
    have h4 := popcount64_toNat_le se
    simp only [Nat.reducePow]
    omega
  | .cellNode _ nw ne sw se, d, h => by
    rw [WFd_cellNode_iff] at h
    obtain ⟨h5, h1, h2, h3, h4⟩ := h
    rw [macroCellSize_cellNode]
    have e1 := macroCellSize_le_pow h1
    have e2 := macroCellSize_le_pow h2
    have e3 := macroCellSize_le_pow h3
    have e4 := macroCellSize_le_pow h4
    have hp : 4 ^ d = 4 * 4 ^ (d - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    omega

theorem leafAt_pos {l : UInt64} {x y : ℤ} (h : leafAt l x y = true) : 0 < (popcount64 l).toNat := by
  have hl : l ≠ 0 := by
    intro hz
    rw [hz, leafAt_zero] at h
    cases h
  have : popcount64 l ≠ 0 := fun hz => hl ((popcount64_eq_zero_iff l).mp hz)
  have h0 : (popcount64 l).toNat ≠ 0 := fun hz => this (UInt32.toNat_inj.mp (by simpa using hz))
  omega

theorem cellAt_pos : ∀ {m : MacroCell} {x y : ℤ}, cellAt m x y = true → 0 < macroCellSize m
  | .level4Node _ nw ne sw se, x, y, h => by
    rw [macroCellSize_level4Node]
    rw [cellAt_level4Node] at h
    rcases quadSel_true_cases h with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, h⟩ <;> have := leafAt_pos h <;> omega
  | .cellNode _ nw ne sw se, x, y, h => by
    rw [macroCellSize_cellNode]
    rw [cellAt_cellNode] at h
    rcases quadSel_true_cases h with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, h⟩ <;> have := cellAt_pos h <;> omega

-- =========================================================================
-- Leaf Chunk Occupancy
-- =========================================================================

theorem leafAt_chunk_se {l : UInt64} {x y : ℤ} (h : leafAt l x y = true) :
    (4 ≤ x ∧ 4 ≤ y) ∨ 0 < (popcount64 (l &&& 0x0000FFFFFFFFFFFF)).toNat := by
  have hb := leafAt_bounds h
  by_cases hr : 4 ≤ x ∧ 4 ≤ y
  · exact Or.inl hr
  · right
    have hne : l &&& 0x0000FFFFFFFFFFFF ≠ 0 := by
      have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
      have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [leafAt, mortonIndex, Int.reduceLT, Int.reduceLE, Int.reduceToNat, Nat.reduceMod,
          Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, and_self] at h
         exact UInt64.and_ne_zero_of_getLsbD h (by decide))
    have hpc : popcount64 (l &&& 0x0000FFFFFFFFFFFF) ≠ 0 :=
      fun hz => hne ((popcount64_eq_zero_iff _).mp hz)
    have h0 : (popcount64 (l &&& 0x0000FFFFFFFFFFFF)).toNat ≠ 0 :=
      fun hz => hpc (UInt32.toNat_inj.mp (by simpa using hz))
    omega

theorem leafAt_chunk_sw {l : UInt64} {x y : ℤ} (h : leafAt l x y = true) :
    (x < 4 ∧ 4 ≤ y) ∨ 0 < (popcount64 (l &&& 0xFFFF0000FFFFFFFF)).toNat := by
  have hb := leafAt_bounds h
  by_cases hr : x < 4 ∧ 4 ≤ y
  · exact Or.inl hr
  · right
    have hne : l &&& 0xFFFF0000FFFFFFFF ≠ 0 := by
      have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
      have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [leafAt, mortonIndex, Int.reduceLT, Int.reduceLE, Int.reduceToNat, Nat.reduceMod,
          Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, and_self] at h
         exact UInt64.and_ne_zero_of_getLsbD h (by decide))
    have hpc : popcount64 (l &&& 0xFFFF0000FFFFFFFF) ≠ 0 :=
      fun hz => hne ((popcount64_eq_zero_iff _).mp hz)
    have h0 : (popcount64 (l &&& 0xFFFF0000FFFFFFFF)).toNat ≠ 0 :=
      fun hz => hpc (UInt32.toNat_inj.mp (by simpa using hz))
    omega

theorem leafAt_chunk_ne {l : UInt64} {x y : ℤ} (h : leafAt l x y = true) :
    (4 ≤ x ∧ y < 4) ∨ 0 < (popcount64 (l &&& 0xFFFFFFFF0000FFFF)).toNat := by
  have hb := leafAt_bounds h
  by_cases hr : 4 ≤ x ∧ y < 4
  · exact Or.inl hr
  · right
    have hne : l &&& 0xFFFFFFFF0000FFFF ≠ 0 := by
      have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
      have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [leafAt, mortonIndex, Int.reduceLT, Int.reduceLE, Int.reduceToNat, Nat.reduceMod,
          Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, and_self] at h
         exact UInt64.and_ne_zero_of_getLsbD h (by decide))
    have hpc : popcount64 (l &&& 0xFFFFFFFF0000FFFF) ≠ 0 :=
      fun hz => hne ((popcount64_eq_zero_iff _).mp hz)
    have h0 : (popcount64 (l &&& 0xFFFFFFFF0000FFFF)).toNat ≠ 0 :=
      fun hz => hpc (UInt32.toNat_inj.mp (by simpa using hz))
    omega

theorem leafAt_chunk_nw {l : UInt64} {x y : ℤ} (h : leafAt l x y = true) :
    (x < 4 ∧ y < 4) ∨ 0 < (popcount64 (l &&& 0xFFFFFFFFFFFF0000)).toNat := by
  have hb := leafAt_bounds h
  by_cases hr : x < 4 ∧ y < 4
  · exact Or.inl hr
  · right
    have hne : l &&& 0xFFFFFFFFFFFF0000 ≠ 0 := by
      have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
      have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (simp only [leafAt, mortonIndex, Int.reduceLT, Int.reduceLE, Int.reduceToNat, Nat.reduceMod,
          Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, and_self] at h
         exact UInt64.and_ne_zero_of_getLsbD h (by decide))
    have hpc : popcount64 (l &&& 0xFFFFFFFFFFFF0000) ≠ 0 :=
      fun hz => hne ((popcount64_eq_zero_iff _).mp hz)
    have h0 : (popcount64 (l &&& 0xFFFFFFFFFFFF0000)).toNat ≠ 0 :=
      fun hz => hpc (UInt32.toNat_inj.mp (by simpa using hz))
    omega

-- =========================================================================
-- Confinement of Unexpanded Nodes
-- =========================================================================

theorem popcount64_zero_toNat : (popcount64 0).toNat = 0 := by decide

/-- Turns a UInt32 identity between sums of popcounts into the corresponding identity on naturals. -/
theorem popcount64_sum2_toNat {a b c : UInt64} (h : popcount64 a = popcount64 b + popcount64 c) :
    (popcount64 a).toNat = (popcount64 b).toNat + (popcount64 c).toNat := by
  have hb := popcount64_toNat_le b
  have hc := popcount64_toNat_le c
  rw [h, UInt32.toNat_add]
  omega

theorem popcount64_sum4_toNat {a b c d e : UInt64}
    (h : popcount64 a = popcount64 b + popcount64 c + popcount64 d + popcount64 e) :
    (popcount64 a).toNat =
    (popcount64 b).toNat + (popcount64 c).toNat + (popcount64 d).toNat + (popcount64 e).toNat := by
  have hb := popcount64_toNat_le b
  have hc := popcount64_toNat_le c
  have hd := popcount64_toNat_le d
  have he := popcount64_toNat_le e
  rw [h, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add]
  omega

set_option maxHeartbeats 1000000 in
/--
A level 5 node whose centered sub-subnode has the same population lies within the central 8x8.
-/
theorem confine_level5 {m : MacroCell} (hm : WFd m 5) (hpop : macroCellSize m < 2 ^ 64)
    (hsz : (centeredSubSubnode m).size = m.size) :
    ∀ x y, cellAt m x y = true → 12 ≤ x ∧ x < 20 ∧ 12 ≤ y ∧ y < 20 := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨ha, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
  obtain ⟨hb, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
  obtain ⟨hc, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
  obtain ⟨hd, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
  have hcss : centeredSubSubnode (.cellNode h (.level4Node ha a1 a2 a3 a4) (.level4Node hb b1 b2 b3 b4)
      (.level4Node hc c1 c2 c3 c4) (.level4Node hd d1 d2 d3 d4)) =
      makeLevel4Node 0 0 0 (centeredSubnodeLevel4 a4 b3 c2 d1) := rfl
  rw [hcss] at hsz
  have e1 := congrArg UInt64.toNat hsz
  rw [size_toNat, size_toNat] at e1
  simp only [makeLevel4Node, macroCellSize_level4Node, macroCellSize_cellNode,
    popcount64_zero_toNat] at e1 hpop
  have pc := popcount64_sum4_toNat (popcount64_centeredSubnodeLevel4 a4 b3 c2 d1)
  have s1 := popcount64_sum2_toNat (popcount64_split_se a4)
  have s2 := popcount64_sum2_toNat (popcount64_split_sw b3)
  have s3 := popcount64_sum2_toNat (popcount64_split_ne c2)
  have s4 := popcount64_sum2_toNat (popcount64_split_nw d1)
  have hle := popcount64_toNat_le (centeredSubnodeLevel4 a4 b3 c2 d1)
  have hsum := e1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hpop] at hsum
  rw [pc] at hsum
  clear e1 hpop pc hle hsz hcss
  intro x y hxy
  simp only [cellAt_cellNode_fun, cellAt_level4Node_fun, level4Node_level_toNat,
    show (2 : ℤ) ^ 4 = 16 by decide] at hxy
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  first
  | (have := leafAt_pos hxy; omega)
  | (rcases leafAt_chunk_se hxy with hr | hr <;> omega)
  | (rcases leafAt_chunk_sw hxy with hr | hr <;> omega)
  | (rcases leafAt_chunk_ne hxy with hr | hr <;> omega)
  | (rcases leafAt_chunk_nw hxy with hr | hr <;> omega)

set_option maxHeartbeats 4000000 in
/--
A level 6 node whose centered sub-subnode has the same population lies within its central 16x16.
-/
theorem confine_level6 {m : MacroCell} (hm : WFd m 6) (hpop : macroCellSize m < 2 ^ 64)
    (hsz : (centeredSubSubnode m).size = m.size) :
    ∀ x y, cellAt m x y = true → 24 ≤ x ∧ x < 40 ∧ 24 ≤ y ∧ y < 40 := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨hA0, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
  obtain ⟨hB0, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
  obtain ⟨hC0, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
  obtain ⟨hD0, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
  obtain ⟨hA10, a11, a12, a13, a14, rfl⟩ := WFd_level4 hA1
  obtain ⟨hA20, a21, a22, a23, a24, rfl⟩ := WFd_level4 hA2
  obtain ⟨hA30, a31, a32, a33, a34, rfl⟩ := WFd_level4 hA3
  obtain ⟨hA40, a41, a42, a43, a44, rfl⟩ := WFd_level4 hA4
  obtain ⟨hB10, b11, b12, b13, b14, rfl⟩ := WFd_level4 hB1
  obtain ⟨hB20, b21, b22, b23, b24, rfl⟩ := WFd_level4 hB2
  obtain ⟨hB30, b31, b32, b33, b34, rfl⟩ := WFd_level4 hB3
  obtain ⟨hB40, b41, b42, b43, b44, rfl⟩ := WFd_level4 hB4
  obtain ⟨hC10, c11, c12, c13, c14, rfl⟩ := WFd_level4 hC1
  obtain ⟨hC20, c21, c22, c23, c24, rfl⟩ := WFd_level4 hC2
  obtain ⟨hC30, c31, c32, c33, c34, rfl⟩ := WFd_level4 hC3
  obtain ⟨hC40, c41, c42, c43, c44, rfl⟩ := WFd_level4 hC4
  obtain ⟨hD10, d11, d12, d13, d14, rfl⟩ := WFd_level4 hD1
  obtain ⟨hD20, d21, d22, d23, d24, rfl⟩ := WFd_level4 hD2
  obtain ⟨hD30, d31, d32, d33, d34, rfl⟩ := WFd_level4 hD3
  obtain ⟨hD40, d41, d42, d43, d44, rfl⟩ := WFd_level4 hD4
  change (makeLevel4Node a44 b33 c22 d11).size = _ at hsz
  have e1 := congrArg UInt64.toNat hsz
  rw [size_toNat, size_toNat] at e1
  simp only [makeLevel4Node, macroCellSize_level4Node, macroCellSize_cellNode] at e1 hpop
  have hsum := e1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hpop] at hsum
  clear e1 hpop hsz
  intro x y hxy
  rw [cellAt_cellNode_width hA (by omega) (show (2 : ℤ) ^ (6 - 1) = 32 by decide)] at hxy
  simp only [cellAt_cellNode_width hA1 (by omega) (show (2 : ℤ) ^ (6 - 1 - 1) = 16 by decide),
    cellAt_cellNode_width hB1 (by omega) (show (2 : ℤ) ^ (6 - 1 - 1) = 16 by decide),
    cellAt_cellNode_width hC1 (by omega) (show (2 : ℤ) ^ (6 - 1 - 1) = 16 by decide),
    cellAt_cellNode_width hD1 (by omega) (show (2 : ℤ) ^ (6 - 1 - 1) = 16 by decide),
    cellAt_level4Node_fun] at hxy
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  first
  | omega
  | (have := leafAt_pos hxy; omega)

set_option maxHeartbeats 4000000 in
/--
A node of level at least 7 whose centered sub-subnode has the same population lies within its
central square of width `2^(K-2)`.
-/
theorem confine_ge7 {m : MacroCell} {K : ℕ} (hm : WFd m K) (h7 : 7 ≤ K) (hK : K < 2 ^ 32)
    (hpop : macroCellSize m < 2 ^ 64) (hsz : (centeredSubSubnode m).size = m.size) :
    ∀ x y, cellAt m x y = true →
      3 * 2 ^ (K - 3) ≤ x ∧ x < 5 * 2 ^ (K - 3) ∧ 3 * 2 ^ (K - 3) ≤ y ∧ y < 5 * 2 ^ (K - 3) := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨hA0, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
  obtain ⟨hB0, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
  obtain ⟨hC0, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
  obtain ⟨hD0, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
  obtain ⟨hA10, A11, A12, A13, A14, rfl, hA11, hA12, hA13, hA14⟩ :=
    WFd_cell hA1 (by omega)
  obtain ⟨hA20, A21, A22, A23, A24, rfl, hA21, hA22, hA23, hA24⟩ :=
    WFd_cell hA2 (by omega)
  obtain ⟨hA30, A31, A32, A33, A34, rfl, hA31, hA32, hA33, hA34⟩ :=
    WFd_cell hA3 (by omega)
  obtain ⟨hA40, A41, A42, A43, A44, rfl, hA41, hA42, hA43, hA44⟩ :=
    WFd_cell hA4 (by omega)
  obtain ⟨hB10, B11, B12, B13, B14, rfl, hB11, hB12, hB13, hB14⟩ :=
    WFd_cell hB1 (by omega)
  obtain ⟨hB20, B21, B22, B23, B24, rfl, hB21, hB22, hB23, hB24⟩ :=
    WFd_cell hB2 (by omega)
  obtain ⟨hB30, B31, B32, B33, B34, rfl, hB31, hB32, hB33, hB34⟩ :=
    WFd_cell hB3 (by omega)
  obtain ⟨hB40, B41, B42, B43, B44, rfl, hB41, hB42, hB43, hB44⟩ :=
    WFd_cell hB4 (by omega)
  obtain ⟨hC10, C11, C12, C13, C14, rfl, hC11, hC12, hC13, hC14⟩ :=
    WFd_cell hC1 (by omega)
  obtain ⟨hC20, C21, C22, C23, C24, rfl, hC21, hC22, hC23, hC24⟩ :=
    WFd_cell hC2 (by omega)
  obtain ⟨hC30, C31, C32, C33, C34, rfl, hC31, hC32, hC33, hC34⟩ :=
    WFd_cell hC3 (by omega)
  obtain ⟨hC40, C41, C42, C43, C44, rfl, hC41, hC42, hC43, hC44⟩ :=
    WFd_cell hC4 (by omega)
  obtain ⟨hD10, D11, D12, D13, D14, rfl, hD11, hD12, hD13, hD14⟩ :=
    WFd_cell hD1 (by omega)
  obtain ⟨hD20, D21, D22, D23, D24, rfl, hD21, hD22, hD23, hD24⟩ :=
    WFd_cell hD2 (by omega)
  obtain ⟨hD30, D31, D32, D33, D34, rfl, hD31, hD32, hD33, hD34⟩ :=
    WFd_cell hD3 (by omega)
  obtain ⟨hD40, D41, D42, D43, D44, rfl, hD41, hD42, hD43, hD44⟩ :=
    WFd_cell hD4 (by omega)
  change (makeCellNode A44 B33 C22 D11).size = _ at hsz
  have e1 := congrArg UInt64.toNat hsz
  rw [size_toNat, size_toNat] at e1
  simp only [makeCellNode, macroCellSize_cellNode] at e1 hpop
  have hsum := e1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hpop] at hsum
  clear e1 hpop hsz
  obtain ⟨e, hev⟩ : ∃ e, (2 : ℤ) ^ (K - 3) = e := ⟨_, rfl⟩
  have w3 : (2 : ℤ) ^ (K - 1 - 1 - 1) = e := by rw [show K - 1 - 1 - 1 = K - 3 by omega, hev]
  have w2 : (2 : ℤ) ^ (K - 1 - 1) = 2 * e := by
    rw [pow_two_pred (K - 1 - 1) (by omega), show K - 1 - 1 - 1 = K - 3 by omega, hev]
  have w1 : (2 : ℤ) ^ (K - 1) = 2 * (2 * e) := by
    rw [pow_two_pred (K - 1) (by omega), show K - 1 - 1 = K - 1 - 1 by rfl, w2]
  rw [hev]
  intro x y hxy
  rw [cellAt_cellNode_width hA (by omega) w1] at hxy
  simp only [cellAt_cellNode_width hA1 (by omega) w2,
    cellAt_cellNode_width hA11 (by omega) w3,
    cellAt_cellNode_width hA21 (by omega) w3,
    cellAt_cellNode_width hA31 (by omega) w3,
    cellAt_cellNode_width hA41 (by omega) w3,
    cellAt_cellNode_width hB1 (by omega) w2,
    cellAt_cellNode_width hB11 (by omega) w3,
    cellAt_cellNode_width hB21 (by omega) w3,
    cellAt_cellNode_width hB31 (by omega) w3,
    cellAt_cellNode_width hB41 (by omega) w3,
    cellAt_cellNode_width hC1 (by omega) w2,
    cellAt_cellNode_width hC11 (by omega) w3,
    cellAt_cellNode_width hC21 (by omega) w3,
    cellAt_cellNode_width hC31 (by omega) w3,
    cellAt_cellNode_width hC41 (by omega) w3,
    cellAt_cellNode_width hD1 (by omega) w2,
    cellAt_cellNode_width hD11 (by omega) w3,
    cellAt_cellNode_width hD21 (by omega) w3,
    cellAt_cellNode_width hD31 (by omega) w3,
    cellAt_cellNode_width hD41 (by omega) w3] at hxy
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  rcases quadSel_true_cases hxy with ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ | ⟨_, _, _, _, hxy⟩ |
    ⟨_, _, _, _, hxy⟩ <;>
  first
  | omega
  | (have := cellAt_pos hxy; omega)

/--
If `needToExpand` is false, the node has level at least 5 and all of its alive cells lie within its
centered sub-subnode, i.e. the central square of width `2^(K-2)`.
-/
theorem confine_of_not_needToExpand {m : MacroCell} {K : ℕ} (hm : WFd m K) (hK : K < 2 ^ 32)
    (hpop : macroCellSize m < 2 ^ 64) (hne : needToExpand m = false) :
    5 ≤ K ∧ ∀ x y, cellAt m x y = true →
      3 * 2 ^ (K - 3) ≤ x ∧ x < 5 * 2 ^ (K - 3) ∧ 3 * 2 ^ (K - 3) ≤ y ∧ y < 5 * 2 ^ (K - 3) := by
  unfold needToExpand at hne
  rw [Bool.or_eq_false_iff] at hne
  obtain ⟨hlev, hsz⟩ := hne
  have hl := WFd_level_toNat hm hK
  have h5 : 5 ≤ K := by
    have : ¬ m.level ≤ 4 := by simpa using hlev
    rw [UInt32.le_iff_toNat_le, hl] at this
    simp only [UInt32.reduceToNat] at this
    omega
  have hsz' : (centeredSubSubnode m).size = m.size := by simpa [centeredSubSubnodeSize] using hsz
  refine ⟨h5, ?_⟩
  by_cases hK5 : K = 5
  · subst hK5
    intro x y hxy
    have := confine_level5 hm hpop hsz' x y hxy
    simp only [show (2 : ℤ) ^ (5 - 3) = 4 by decide]
    omega
  by_cases hK6 : K = 6
  · subst hK6
    intro x y hxy
    have := confine_level6 hm hpop hsz' x y hxy
    simp only [show (2 : ℤ) ^ (6 - 3) = 8 by decide]
    omega
  exact confine_ge7 hm (by omega) hK hpop hsz'

end Algorithm

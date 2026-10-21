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

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Abstract Quadrant Geometry
-- =========================================================================

theorem fn_congr2 (f : ℤ → ℤ → Bool) {a a' b b' : ℤ} (h1 : a = a') (h2 : b = b') :
    f a b = f a' b' := by
  rw [h1, h2]

/-- Rewrites `quadSel` applications whose quadrant is determined by linear arithmetic. -/
macro "quad_descend" : tactic =>
  `(tactic| simp (disch := omega) only [quadSel_nw, quadSel_ne, quadSel_sw, quadSel_se])

/-- Closes `f a b = f a' b'` where the coordinates agree by linear arithmetic. -/
macro "coord_congr" : tactic =>
  `(tactic| first | rfl | (apply fn_congr2 <;> omega))

/--
The centered subnode of a 2-level quadtree is the window offset by a quarter of its width.
-/
theorem quadSel_center (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : ℤ → ℤ → Bool)
    (q : ℤ) (_hq : 0 < q) (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * q) (hy0 : 0 ≤ y) (hy : y < 2 * q) :
    quadSel a4 b3 c2 d1 q x y =
    quadSel (quadSel a1 a2 a3 a4 q) (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q)
      (quadSel d1 d2 d3 d4 q) (2 * q) (x + q) (y + q) := by
  refine quadSel_eq_of_quadrants _ _ _ _ (fun x y => quadSel (quadSel a1 a2 a3 a4 q)
    (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q) (quadSel d1 d2 d3 d4 q) (2 * q) (x + q) (y + q))
    q ?_ ?_ ?_ ?_ x y hx0 hx hy0 hy
  all_goals
    intro x y hx0 hx hy0 hy
    quad_descend
    coord_congr

/--
The horizontally-centered subnode spanning two adjacent 2-level quadtrees.
-/
theorem quadSel_horizontal (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : ℤ → ℤ → Bool)
    (e1 e2 e3 e4 f1 f2 f3 f4 g1 g2 g3 g4 h1 h2 h3 h4 : ℤ → ℤ → Bool)
    (G G' : ℤ → ℤ → Bool) (q : ℤ) (_hq : 0 < q)
    (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * q) (hy0 : 0 ≤ y) (hy : y < 2 * q) :
    quadSel b4 e3 d2 g1 q x y =
    quadSel
      (quadSel (quadSel a1 a2 a3 a4 q) (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q)
        (quadSel d1 d2 d3 d4 q) (2 * q))
      (quadSel (quadSel e1 e2 e3 e4 q) (quadSel f1 f2 f3 f4 q) (quadSel g1 g2 g3 g4 q)
        (quadSel h1 h2 h3 h4 q) (2 * q))
      G G' (4 * q) (x + 3 * q) (y + q) := by
  refine quadSel_eq_of_quadrants _ _ _ _ (fun x y => quadSel
      (quadSel (quadSel a1 a2 a3 a4 q) (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q)
        (quadSel d1 d2 d3 d4 q) (2 * q))
      (quadSel (quadSel e1 e2 e3 e4 q) (quadSel f1 f2 f3 f4 q) (quadSel g1 g2 g3 g4 q)
        (quadSel h1 h2 h3 h4 q) (2 * q))
      G G' (4 * q) (x + 3 * q) (y + q))
    q ?_ ?_ ?_ ?_ x y hx0 hx hy0 hy
  all_goals
    intro x y hx0 hx hy0 hy
    quad_descend
    coord_congr

/--
The vertically-centered subnode spanning two vertically adjacent 2-level quadtrees.
-/
theorem quadSel_vertical (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : ℤ → ℤ → Bool)
    (e1 e2 e3 e4 f1 f2 f3 f4 g1 g2 g3 g4 h1 h2 h3 h4 : ℤ → ℤ → Bool)
    (G G' : ℤ → ℤ → Bool) (q : ℤ) (_hq : 0 < q)
    (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * q) (hy0 : 0 ≤ y) (hy : y < 2 * q) :
    quadSel c4 d3 e2 f1 q x y =
    quadSel
      (quadSel (quadSel a1 a2 a3 a4 q) (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q)
        (quadSel d1 d2 d3 d4 q) (2 * q))
      G
      (quadSel (quadSel e1 e2 e3 e4 q) (quadSel f1 f2 f3 f4 q) (quadSel g1 g2 g3 g4 q)
        (quadSel h1 h2 h3 h4 q) (2 * q))
      G' (4 * q) (x + q) (y + 3 * q) := by
  refine quadSel_eq_of_quadrants _ _ _ _ (fun x y => quadSel
      (quadSel (quadSel a1 a2 a3 a4 q) (quadSel b1 b2 b3 b4 q) (quadSel c1 c2 c3 c4 q)
        (quadSel d1 d2 d3 d4 q) (2 * q))
      G
      (quadSel (quadSel e1 e2 e3 e4 q) (quadSel f1 f2 f3 f4 q) (quadSel g1 g2 g3 g4 q)
        (quadSel h1 h2 h3 h4 q) (2 * q))
      G' (4 * q) (x + q) (y + 3 * q))
    q ?_ ?_ ?_ ?_ x y hx0 hx hy0 hy
  all_goals
    intro x y hx0 hx hy0 hy
    quad_descend
    coord_congr

/-- Closes a goal produced by splitting `quadSel` conditions. -/
macro "quad_finish" : tactic =>
  `(tactic| first | rfl | (exfalso; omega) | (apply fn_congr2 <;> omega))

theorem quadSel_shift_right (f1 f2 f3 f4 g g' : ℤ → ℤ → Bool) (w x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < w) :
    quadSel f1 f2 f3 f4 w (x + w) y = quadSel f2 g f4 g' w x y := by
  unfold quadSel
  repeat' split
  all_goals quad_finish

theorem quadSel_shift_down (f1 f2 f3 f4 g g' : ℤ → ℤ → Bool) (w x y : ℤ)
    (hy0 : 0 ≤ y) (hy : y < w) :
    quadSel f1 f2 f3 f4 w x (y + w) = quadSel f3 f4 g g' w x y := by
  unfold quadSel
  repeat' split
  all_goals quad_finish

-- =========================================================================
-- MacroCell Shape Lemmas
-- =========================================================================

theorem cellAt_cellNode_fun (h : UInt32) (nw ne sw se : MacroCell) :
    cellAt (.cellNode h nw ne sw se) =
    quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) ((2 : ℤ) ^ nw.level.toNat) := by
  funext x y
  rfl

theorem cellAt_level4Node_fun (h : UInt32) (nw ne sw se : UInt64) :
    cellAt (.level4Node h nw ne sw se) =
    quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 := by
  funext x y
  rfl

theorem pow_two_pred (L : ℕ) (h : 1 ≤ L) : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
  rw [← Int.pow_succ']
  congr 1
  omega

theorem pow_two_pos (L : ℕ) : (0 : ℤ) < 2 ^ L := Int.pow_pos (by decide)

-- =========================================================================
-- Centered Subnode Semantics
-- =========================================================================

theorem centeredSubnode_spec {n : MacroCell} {L : ℕ} (hn : WFd n L) (h5 : 5 ≤ L) (hL : L < 2 ^ 32) :
    WFd (centeredSubnode n) (L - 1) ∧
    ∀ x y, 0 ≤ x → x < (2 : ℤ) ^ (L - 1) → 0 ≤ y → y < (2 : ℤ) ^ (L - 1) →
      cellAt (centeredSubnode n) x y = cellAt n (x + 2 ^ (L - 2)) (y + 2 ^ (L - 2)) := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hn h5
  by_cases hL5 : L = 5
  · subst hL5
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    refine ⟨WFd_makeLevel4Node _ _ _ _, ?_⟩
    intro x y hx0 hx hy0 hy
    change cellAt (makeLevel4Node a4 b3 c2 d1) x y = _
    rw [cellAt_makeLevel4Node, cellAt_cellNode_fun, cellAt_level4Node_fun, cellAt_level4Node_fun,
      cellAt_level4Node_fun, cellAt_level4Node_fun]
    exact quadSel_center _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 8 (by decide) x y hx0 hx hy0 hy
  · have h6 : 6 ≤ L := by omega
    obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
    obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
    obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
    obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
    have hw : WFd (makeCellNode A4 B3 C2 D1) (L - 1 - 1 + 1) := WFd_makeCellNode hA4 hB3 hC2 hD1
    rw [show L - 1 - 1 + 1 = L - 1 by omega] at hw
    refine ⟨hw, ?_⟩
    intro x y hx0 hx hy0 hy
    change cellAt (makeCellNode A4 B3 C2 D1) x y = _
    rw [cellAt_makeCellNode, cellAt_cellNode_fun, cellAt_cellNode_fun, cellAt_cellNode_fun,
      cellAt_cellNode_fun, cellAt_cellNode_fun,
      WFd_level_toNat hA (by omega), WFd_level_toNat hA1 (by omega), WFd_level_toNat hA4 (by omega),
      WFd_level_toNat hB1 (by omega), WFd_level_toNat hC1 (by omega), WFd_level_toNat hD1 (by omega),
      show L - 1 - 1 = L - 2 by omega, pow_two_pred (L - 1) (by omega), show L - 1 - 1 = L - 2 by omega]
    rw [pow_two_pred (L - 1) (by omega), show L - 1 - 1 = L - 2 by omega] at hx hy
    exact quadSel_center _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pow_two_pos _) x y hx0 hx hy0 hy

theorem pow_two_five : (2 : ℤ) ^ 5 = 4 * 8 := by decide
theorem pow_two_four : (2 : ℤ) ^ 4 = 2 * 8 := by decide
theorem pow_two_three : (2 : ℤ) ^ 3 = 8 := by decide

theorem level4Node_level_toNat (h : UInt32) (nw ne sw se : UInt64) :
    (MacroCell.level4Node h nw ne sw se).level.toNat = 4 := rfl

theorem centeredHorizontalSubnode_spec {W E : MacroCell} {L : ℕ} (hW : WFd W L) (hE : WFd E L)
    (h5 : 5 ≤ L) (hL : L < 2 ^ 32) :
    WFd (centeredHorizontalSubnode W E) (L - 1) ∧
    ∀ (G G' : ℤ → ℤ → Bool) x y, 0 ≤ x → x < (2 : ℤ) ^ (L - 1) → 0 ≤ y → y < (2 : ℤ) ^ (L - 1) →
      cellAt (centeredHorizontalSubnode W E) x y =
      quadSel (cellAt W) (cellAt E) G G' (2 ^ L) (x + 3 * 2 ^ (L - 2)) (y + 2 ^ (L - 2)) := by
  obtain ⟨_, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hW h5
  obtain ⟨_, E', F, G, H, rfl, hE', hF, hG, hH⟩ := WFd_cell hE h5
  by_cases hL5 : L = 5
  · subst hL5
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    obtain ⟨_, e1, e2, e3, e4, rfl⟩ := WFd_level4 hE'
    obtain ⟨_, f1, f2, f3, f4, rfl⟩ := WFd_level4 hF
    obtain ⟨_, g1, g2, g3, g4, rfl⟩ := WFd_level4 hG
    obtain ⟨_, h1, h2, h3, h4, rfl⟩ := WFd_level4 hH
    refine ⟨WFd_makeLevel4Node _ _ _ _, ?_⟩
    intro G G' x y hx0 hx hy0 hy
    change cellAt (makeLevel4Node b4 e3 d2 g1) x y = _
    rw [cellAt_makeLevel4Node]
    simp only [cellAt_cellNode_fun, cellAt_level4Node_fun, level4Node_level_toNat, pow_two_five,
      pow_two_four, show 5 - 2 = 3 from rfl, pow_two_three]
    exact quadSel_horizontal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G G' 8
      (by decide) x y hx0 hx hy0 hy
  · obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
    obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
    obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
    obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
    obtain ⟨_, E1, E2, E3, E4, rfl, hE1, hE2, hE3, hE4⟩ := WFd_cell hE' (by omega)
    obtain ⟨_, F1, F2, F3, F4, rfl, hF1, hF2, hF3, hF4⟩ := WFd_cell hF (by omega)
    obtain ⟨_, G1, G2, G3, G4, rfl, hG1, hG2, hG3, hG4⟩ := WFd_cell hG (by omega)
    obtain ⟨_, H1, H2, H3, H4, rfl, hH1, hH2, hH3, hH4⟩ := WFd_cell hH (by omega)
    have hw : WFd (makeCellNode B4 E3 D2 G1) (L - 1 - 1 + 1) := WFd_makeCellNode hB4 hE3 hD2 hG1
    rw [show L - 1 - 1 + 1 = L - 1 by omega] at hw
    refine ⟨hw, ?_⟩
    intro G' G'' x y hx0 hx hy0 hy
    change cellAt (makeCellNode B4 E3 D2 G1) x y = _
    rw [cellAt_makeCellNode]
    simp only [cellAt_cellNode_fun,
      WFd_level_toNat hA (by omega), WFd_level_toNat hE' (by omega),
      WFd_level_toNat hA1 (by omega), WFd_level_toNat hB1 (by omega), WFd_level_toNat hB4 (by omega),
      WFd_level_toNat hC1 (by omega), WFd_level_toNat hD1 (by omega), WFd_level_toNat hE1 (by omega),
      WFd_level_toNat hF1 (by omega), WFd_level_toNat hG1 (by omega), WFd_level_toNat hH1 (by omega),
      show L - 1 - 1 = L - 2 by omega]
    have p1 : (2 : ℤ) ^ (L - 1) = 2 * 2 ^ (L - 2) := by
      rw [pow_two_pred (L - 1) (by omega), show L - 1 - 1 = L - 2 by omega]
    have p2 : (2 : ℤ) ^ L = 4 * 2 ^ (L - 2) := by
      rw [pow_two_pred L (by omega), p1]; omega
    rw [p1, p2]
    rw [p1] at hx hy
    exact quadSel_horizontal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G' G''
      _ (pow_two_pos _) x y hx0 hx hy0 hy

theorem centeredVerticalSubnode_spec {N S : MacroCell} {L : ℕ} (hN : WFd N L) (hS : WFd S L)
    (h5 : 5 ≤ L) (hL : L < 2 ^ 32) :
    WFd (centeredVerticalSubnode N S) (L - 1) ∧
    ∀ (G G' : ℤ → ℤ → Bool) x y, 0 ≤ x → x < (2 : ℤ) ^ (L - 1) → 0 ≤ y → y < (2 : ℤ) ^ (L - 1) →
      cellAt (centeredVerticalSubnode N S) x y =
      quadSel (cellAt N) G (cellAt S) G' (2 ^ L) (x + 2 ^ (L - 2)) (y + 3 * 2 ^ (L - 2)) := by
  obtain ⟨_, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hN h5
  obtain ⟨_, E', F, G, H, rfl, hE', hF, hG, hH⟩ := WFd_cell hS h5
  by_cases hL5 : L = 5
  · subst hL5
    obtain ⟨_, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
    obtain ⟨_, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
    obtain ⟨_, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
    obtain ⟨_, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
    obtain ⟨_, e1, e2, e3, e4, rfl⟩ := WFd_level4 hE'
    obtain ⟨_, f1, f2, f3, f4, rfl⟩ := WFd_level4 hF
    obtain ⟨_, g1, g2, g3, g4, rfl⟩ := WFd_level4 hG
    obtain ⟨_, h1, h2, h3, h4, rfl⟩ := WFd_level4 hH
    refine ⟨WFd_makeLevel4Node _ _ _ _, ?_⟩
    intro G G' x y hx0 hx hy0 hy
    change cellAt (makeLevel4Node c4 d3 e2 f1) x y = _
    rw [cellAt_makeLevel4Node]
    simp only [cellAt_cellNode_fun, cellAt_level4Node_fun, level4Node_level_toNat, pow_two_five,
      pow_two_four, show 5 - 2 = 3 from rfl, pow_two_three]
    exact quadSel_vertical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G G' 8
      (by decide) x y hx0 hx hy0 hy
  · obtain ⟨_, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
    obtain ⟨_, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
    obtain ⟨_, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
    obtain ⟨_, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
    obtain ⟨_, E1, E2, E3, E4, rfl, hE1, hE2, hE3, hE4⟩ := WFd_cell hE' (by omega)
    obtain ⟨_, F1, F2, F3, F4, rfl, hF1, hF2, hF3, hF4⟩ := WFd_cell hF (by omega)
    obtain ⟨_, G1, G2, G3, G4, rfl, hG1, hG2, hG3, hG4⟩ := WFd_cell hG (by omega)
    obtain ⟨_, H1, H2, H3, H4, rfl, hH1, hH2, hH3, hH4⟩ := WFd_cell hH (by omega)
    have hw : WFd (makeCellNode C4 D3 E2 F1) (L - 1 - 1 + 1) := WFd_makeCellNode hC4 hD3 hE2 hF1
    rw [show L - 1 - 1 + 1 = L - 1 by omega] at hw
    refine ⟨hw, ?_⟩
    intro G' G'' x y hx0 hx hy0 hy
    change cellAt (makeCellNode C4 D3 E2 F1) x y = _
    rw [cellAt_makeCellNode]
    simp only [cellAt_cellNode_fun,
      WFd_level_toNat hA (by omega), WFd_level_toNat hE' (by omega),
      WFd_level_toNat hA1 (by omega), WFd_level_toNat hB1 (by omega), WFd_level_toNat hC4 (by omega),
      WFd_level_toNat hC1 (by omega), WFd_level_toNat hD1 (by omega), WFd_level_toNat hE1 (by omega),
      WFd_level_toNat hF1 (by omega), WFd_level_toNat hG1 (by omega), WFd_level_toNat hH1 (by omega),
      show L - 1 - 1 = L - 2 by omega]
    have p1 : (2 : ℤ) ^ (L - 1) = 2 * 2 ^ (L - 2) := by
      rw [pow_two_pred (L - 1) (by omega), show L - 1 - 1 = L - 2 by omega]
    have p2 : (2 : ℤ) ^ L = 4 * 2 ^ (L - 2) := by
      rw [pow_two_pred L (by omega), p1]; omega
    rw [p1, p2]
    rw [p1] at hx hy
    exact quadSel_vertical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G' G''
      _ (pow_two_pos _) x y hx0 hx hy0 hy

-- =========================================================================
-- Abstract Stepping Assembly
-- =========================================================================

/--
Four sub-squares of width `2e`, each agreeing with a shifted parent function, assemble into a
quadrant of width `4e` agreeing with the parent function.
-/
theorem quadrant_of_pieces (P1 P2 P3 P4 M : ℤ → ℤ → Bool) (e ox oy : ℤ)
    (h1 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → P1 x y = M (x + ox) (y + oy))
    (h2 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → P2 x y = M (x + (ox + 2 * e)) (y + oy))
    (h3 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → P3 x y = M (x + ox) (y + (oy + 2 * e)))
    (h4 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
      P4 x y = M (x + (ox + 2 * e)) (y + (oy + 2 * e)))
    (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * (2 * e)) (hy0 : 0 ≤ y) (hy : y < 2 * (2 * e)) :
    quadSel P1 P2 P3 P4 (2 * e) x y = M (x + ox) (y + oy) := by
  refine quadSel_eq_of_quadrants _ _ _ _ (fun x y => M (x + ox) (y + oy)) (2 * e) ?_ ?_ ?_ ?_
    x y hx0 hx hy0 hy
  · exact h1
  · intro x y hx0 hx hy0 hy
    rw [h2 x y hx0 hx hy0 hy]
    coord_congr
  · intro x y hx0 hx hy0 hy
    rw [h3 x y hx0 hx hy0 hy]
    coord_congr
  · intro x y hx0 hx hy0 hy
    rw [h4 x y hx0 hx hy0 hy]
    coord_congr

/--
If each of four overlapping quadrants (of width `4e`, offset by `e` and `3e` in the parent)
steps correctly to its center, the four results assemble into the stepped center of the parent.
-/
theorem step_assembly (M Q1 Q2 Q3 Q4 R1 R2 R3 R4 : ℤ → ℤ → Bool) (e : ℤ) (_he : 1 ≤ e)
    (hQ1 : ∀ x y, 0 ≤ x → x < 2 * (2 * e) → 0 ≤ y → y < 2 * (2 * e) → Q1 x y = M (x + e) (y + e))
    (hQ2 : ∀ x y, 0 ≤ x → x < 2 * (2 * e) → 0 ≤ y → y < 2 * (2 * e) →
      Q2 x y = M (x + 3 * e) (y + e))
    (hQ3 : ∀ x y, 0 ≤ x → x < 2 * (2 * e) → 0 ≤ y → y < 2 * (2 * e) →
      Q3 x y = M (x + e) (y + 3 * e))
    (hQ4 : ∀ x y, 0 ≤ x → x < 2 * (2 * e) → 0 ≤ y → y < 2 * (2 * e) →
      Q4 x y = M (x + 3 * e) (y + 3 * e))
    (hR1 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → R1 x y = nextGenAt Q1 (x + e) (y + e))
    (hR2 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → R2 x y = nextGenAt Q2 (x + e) (y + e))
    (hR3 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → R3 x y = nextGenAt Q3 (x + e) (y + e))
    (hR4 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → R4 x y = nextGenAt Q4 (x + e) (y + e))
    (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * (2 * e)) (hy0 : 0 ≤ y) (hy : y < 2 * (2 * e)) :
    quadSel R1 R2 R3 R4 (2 * e) x y = nextGenAt M (x + 2 * e) (y + 2 * e) := by
  refine quadSel_eq_of_quadrants _ _ _ _ (fun x y => nextGenAt M (x + 2 * e) (y + 2 * e)) (2 * e)
    ?_ ?_ ?_ ?_ x y hx0 hx hy0 hy
  · intro x y hx0 hx hy0 hy
    rw [hR1 x y hx0 hx hy0 hy]
    apply nextGenAt_congr
    intro dx dy h1 h2 h3 h4
    rw [hQ1 _ _ (by omega) (by omega) (by omega) (by omega)]
    coord_congr
  · intro x y hx0 hx hy0 hy
    rw [hR2 x y hx0 hx hy0 hy]
    apply nextGenAt_congr
    intro dx dy h1 h2 h3 h4
    rw [hQ2 _ _ (by omega) (by omega) (by omega) (by omega)]
    coord_congr
  · intro x y hx0 hx hy0 hy
    rw [hR3 x y hx0 hx hy0 hy]
    apply nextGenAt_congr
    intro dx dy h1 h2 h3 h4
    rw [hQ3 _ _ (by omega) (by omega) (by omega) (by omega)]
    coord_congr
  · intro x y hx0 hx hy0 hy
    rw [hR4 x y hx0 hx hy0 hy]
    apply nextGenAt_congr
    intro dx dy h1 h2 h3 h4
    rw [hQ4 _ _ (by omega) (by omega) (by omega) (by omega)]
    coord_congr

-- =========================================================================
-- Level 5 Stepping (base case of the recursion)
-- =========================================================================

/-- Proves a leaf-piece equation for a level 5 node by case analysis on the 4x4 sub-quadrant. -/
macro "level5_piece" : tactic =>
  `(tactic| (
    intro x y hx0 hx hy0 hy
    rw [leafAt_centeredSubnodeLevel4 _ _ _ _ x y hx0 hx hy0 hy]
    simp +zetaDelta only [cellAt_cellNode_fun, cellAt_level4Node_fun, level4Node_level_toNat, pow_two_four]
    by_cases hx4 : x < 4 <;> by_cases hy4 : y < 4 <;> quad_descend <;> coord_congr))

theorem step_level5_spec {m : MacroCell} (hm : WFd m 5) (fuel : ℕ) :
    WFd (hashLifeStepRecursiveAux (fuel + 1) m) 4 ∧
    ∀ x y, 0 ≤ x → x < 16 → 0 ≤ y → y < 16 →
      cellAt (hashLifeStepRecursiveAux (fuel + 1) m) x y = nextGenAt (cellAt m) (x + 8) (y + 8) := by
  obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm (by omega)
  obtain ⟨ha, a1, a2, a3, a4, rfl⟩ := WFd_level4 hA
  obtain ⟨hb, b1, b2, b3, b4, rfl⟩ := WFd_level4 hB
  obtain ⟨hc, c1, c2, c3, c4, rfl⟩ := WFd_level4 hC
  obtain ⟨hd, d1, d2, d3, d4, rfl⟩ := WFd_level4 hD
  refine ⟨rfl, ?_⟩
  intro x y hx0 hx hy0 hy
  let M := cellAt (.cellNode h (.level4Node ha a1 a2 a3 a4) (.level4Node hb b1 b2 b3 b4)
    (.level4Node hc c1 c2 c3 c4) (.level4Node hd d1 d2 d3 d4))
  let n00 := centeredSubnodeLevel4 a1 a2 a3 a4
  let n01 := centeredSubnodeLevel4 a2 b1 a4 b3
  let n02 := centeredSubnodeLevel4 b1 b2 b3 b4
  let n10 := centeredSubnodeLevel4 a3 a4 c1 c2
  let n11 := centeredSubnodeLevel4 a4 b3 c2 d1
  let n12 := centeredSubnodeLevel4 b3 b4 d1 d2
  let n20 := centeredSubnodeLevel4 c1 c2 c3 c4
  let n21 := centeredSubnodeLevel4 c2 d1 c4 d3
  let n22 := centeredSubnodeLevel4 d1 d2 d3 d4
  have p00 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n00 x y = M (x + 4) (y + 4) := by
    level5_piece
  have p01 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n01 x y = M (x + 12) (y + 4) := by
    level5_piece
  have p02 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n02 x y = M (x + 20) (y + 4) := by
    level5_piece
  have p10 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n10 x y = M (x + 4) (y + 12) := by
    level5_piece
  have p11 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n11 x y = M (x + 12) (y + 12) := by
    level5_piece
  have p12 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n12 x y = M (x + 20) (y + 12) := by
    level5_piece
  have p20 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n20 x y = M (x + 4) (y + 20) := by
    level5_piece
  have p21 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n21 x y = M (x + 12) (y + 20) := by
    level5_piece
  have p22 : ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → leafAt n22 x y = M (x + 20) (y + 20) := by
    level5_piece
  have quad : ∀ (P1 P2 P3 P4 : ℤ → ℤ → Bool) (ox oy : ℤ),
      (∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P1 x y = M (x + ox) (y + oy)) →
      (∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P2 x y = M (x + (ox + 8)) (y + oy)) →
      (∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P3 x y = M (x + ox) (y + (oy + 8))) →
      (∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P4 x y = M (x + (ox + 8)) (y + (oy + 8))) →
      ∀ x y, 0 ≤ x → x < 2 * (2 * 4) → 0 ≤ y → y < 2 * (2 * 4) →
        quadSel P1 P2 P3 P4 8 x y = M (x + ox) (y + oy) :=
    fun P1 P2 P3 P4 ox oy h1 h2 h3 h4 => quadrant_of_pieces P1 P2 P3 P4 M 4 ox oy h1 h2 h3 h4
  have shift : ∀ (P : ℤ → ℤ → Bool) (a b a' b' : ℤ),
      (∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P x y = M (x + a) (y + b)) → a = a' → b = b' →
      ∀ x y, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → P x y = M (x + a') (y + b') := by
    intro P a b a' b' hP ha hb
    subst ha hb
    exact hP
  have hQ1 := quad _ _ _ _ 4 4 p00 (shift _ _ _ _ _ p01 (by decide) rfl)
    (shift _ _ _ _ _ p10 rfl (by decide)) (shift _ _ _ _ _ p11 (by decide) (by decide))
  have hQ2 := quad _ _ _ _ 12 4 p01 (shift _ _ _ _ _ p02 (by decide) rfl)
    (shift _ _ _ _ _ p11 rfl (by decide)) (shift _ _ _ _ _ p12 (by decide) (by decide))
  have hQ3 := quad _ _ _ _ 4 12 p10 (shift _ _ _ _ _ p11 (by decide) rfl)
    (shift _ _ _ _ _ p20 rfl (by decide)) (shift _ _ _ _ _ p21 (by decide) (by decide))
  have hQ4 := quad _ _ _ _ 12 12 p11 (shift _ _ _ _ _ p12 (by decide) rfl)
    (shift _ _ _ _ _ p21 rfl (by decide)) (shift _ _ _ _ _ p22 (by decide) (by decide))
  exact step_assembly M _ _ _ _
    (leafAt (computeLevel4NextGen16x16UInt n00 n01 n10 n11))
    (leafAt (computeLevel4NextGen16x16UInt n01 n02 n11 n12))
    (leafAt (computeLevel4NextGen16x16UInt n10 n11 n20 n21))
    (leafAt (computeLevel4NextGen16x16UInt n11 n12 n21 n22))
    4 (by decide) hQ1 (by simpa using hQ2) (by simpa using hQ3) (by simpa using hQ4)
    (leafAt_computeLevel4NextGen16x16UInt _ _ _ _) (leafAt_computeLevel4NextGen16x16UInt _ _ _ _)
    (leafAt_computeLevel4NextGen16x16UInt _ _ _ _) (leafAt_computeLevel4NextGen16x16UInt _ _ _ _)
    x y hx0 hx hy0 hy

-- =========================================================================
-- Subnode Specifications in Terms of the Eighth-Width
-- =========================================================================

theorem pow_two_sub_two {L : ℕ} {e : ℤ} (h2 : 2 ≤ L) (he : (2 : ℤ) ^ (L - 2) = e) :
    (2 : ℤ) ^ (L - 1) = 2 * e ∧ (2 : ℤ) ^ L = 2 * (2 * e) := by
  have h1 : (2 : ℤ) ^ (L - 1) = 2 * e := by
    rw [pow_two_pred (L - 1) (by omega), show L - 1 - 1 = L - 2 by omega, he]
  exact ⟨h1, by rw [pow_two_pred L (by omega), h1]⟩

theorem cs_spec {n : MacroCell} {L : ℕ} {e : ℤ} (hn : WFd n L) (h5 : 5 ≤ L) (hL : L < 2 ^ 32)
    (he : (2 : ℤ) ^ (L - 2) = e) :
    WFd (centeredSubnode n) (L - 1) ∧
    ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
      cellAt (centeredSubnode n) x y = cellAt n (x + e) (y + e) := by
  obtain ⟨hw, hs⟩ := centeredSubnode_spec hn h5 hL
  obtain ⟨p1, _⟩ := pow_two_sub_two (by omega) he
  refine ⟨hw, fun x y hx0 hx hy0 hy => ?_⟩
  rw [hs x y hx0 (by omega) hy0 (by omega), he]

theorem chs_spec {W E : MacroCell} {L : ℕ} {e : ℤ} (hW : WFd W L) (hE : WFd E L) (h5 : 5 ≤ L)
    (hL : L < 2 ^ 32) (he : (2 : ℤ) ^ (L - 2) = e) :
    WFd (centeredHorizontalSubnode W E) (L - 1) ∧
    ∀ (G G' : ℤ → ℤ → Bool) x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
      cellAt (centeredHorizontalSubnode W E) x y =
      quadSel (cellAt W) (cellAt E) G G' (2 * (2 * e)) (x + 3 * e) (y + e) := by
  obtain ⟨hw, hs⟩ := centeredHorizontalSubnode_spec hW hE h5 hL
  obtain ⟨p1, p2⟩ := pow_two_sub_two (by omega) he
  refine ⟨hw, fun G G' x y hx0 hx hy0 hy => ?_⟩
  rw [hs G G' x y hx0 (by omega) hy0 (by omega), he, p2]

theorem cvs_spec {N S : MacroCell} {L : ℕ} {e : ℤ} (hN : WFd N L) (hS : WFd S L) (h5 : 5 ≤ L)
    (hL : L < 2 ^ 32) (he : (2 : ℤ) ^ (L - 2) = e) :
    WFd (centeredVerticalSubnode N S) (L - 1) ∧
    ∀ (G G' : ℤ → ℤ → Bool) x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
      cellAt (centeredVerticalSubnode N S) x y =
      quadSel (cellAt N) G (cellAt S) G' (2 * (2 * e)) (x + e) (y + 3 * e) := by
  obtain ⟨hw, hs⟩ := centeredVerticalSubnode_spec hN hS h5 hL
  obtain ⟨p1, p2⟩ := pow_two_sub_two (by omega) he
  refine ⟨hw, fun G G' x y hx0 hx hy0 hy => ?_⟩
  rw [hs G G' x y hx0 (by omega) hy0 (by omega), he, p2]

-- =========================================================================
-- Recursive Stepping Correctness
-- =========================================================================

theorem piece_retarget {P M : ℤ → ℤ → Bool} {w a b a' b' : ℤ}
    (hP : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → P x y = M (x + a) (y + b)) (ha : a = a') (hb : b = b') :
    ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → P x y = M (x + a') (y + b') := by
  subst ha hb
  exact hP

theorem cellAt_cellNode_width {h : UInt32} {nw ne sw se : MacroCell} {L : ℕ} {w : ℤ}
    (hnw : WFd nw L) (hL : L < 2 ^ 32) (hw : (2 : ℤ) ^ L = w) :
    cellAt (.cellNode h nw ne sw se) = quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) w := by
  rw [cellAt_cellNode_fun, WFd_level_toNat hnw hL, hw]

theorem cellAt_makeCellNode_width {nw ne sw se : MacroCell} {L : ℕ} {w : ℤ}
    (hnw : WFd nw L) (hL : L < 2 ^ 32) (hw : (2 : ℤ) ^ L = w) :
    cellAt (makeCellNode nw ne sw se) = quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) w :=
  cellAt_cellNode_width hnw hL hw

/--
Correctness of the recursive HashLife step: a well-formed node of level `K ≥ 5` steps to a node of
level `K - 1` holding the next generation of its central `2^(K-1)` square.
-/
theorem hashLifeStepRecursiveAux_spec : ∀ (fuel : ℕ) {m : MacroCell} {K : ℕ},
    WFd m K → 5 ≤ K → K < 2 ^ 32 → K ≤ fuel + 4 →
    WFd (hashLifeStepRecursiveAux fuel m) (K - 1) ∧
    ∀ x y, 0 ≤ x → x < (2 : ℤ) ^ (K - 1) → 0 ≤ y → y < (2 : ℤ) ^ (K - 1) →
      cellAt (hashLifeStepRecursiveAux fuel m) x y =
      nextGenAt (cellAt m) (x + 2 ^ (K - 2)) (y + 2 ^ (K - 2))
  | 0, _, _, _, h5, _, hf => by omega
  | fuel + 1, m, K, hm, h5, hK, hf => by
    by_cases hK5 : K = 5
    · subst hK5
      obtain ⟨hw, hs⟩ := step_level5_spec hm fuel
      exact ⟨hw, hs⟩
    obtain ⟨h, A, B, C, D, rfl, hA, hB, hC, hD⟩ := WFd_cell hm h5
    obtain ⟨hA0, A1, A2, A3, A4, rfl, hA1, hA2, hA3, hA4⟩ := WFd_cell hA (by omega)
    obtain ⟨hB0, B1, B2, B3, B4, rfl, hB1, hB2, hB3, hB4⟩ := WFd_cell hB (by omega)
    obtain ⟨hC0, C1, C2, C3, C4, rfl, hC1, hC2, hC3, hC4⟩ := WFd_cell hC (by omega)
    obtain ⟨hD0, D1, D2, D3, D4, rfl, hD1, hD2, hD3, hD4⟩ := WFd_cell hD (by omega)
    -- Name the children; only their well-formedness is needed from here on.
    generalize hA' : MacroCell.cellNode hA0 A1 A2 A3 A4 = A at *
    generalize hB' : MacroCell.cellNode hB0 B1 B2 B3 B4 = B at *
    generalize hC' : MacroCell.cellNode hC0 C1 C2 C3 C4 = C at *
    generalize hD' : MacroCell.cellNode hD0 D1 D2 D3 D4 = D at *
    have hstep : hashLifeStepRecursiveAux (fuel + 1) (.cellNode h A B C D) =
        makeCellNode
          (hashLifeStepRecursiveAux fuel (makeCellNode (centeredSubnode A)
            (centeredHorizontalSubnode A B) (centeredVerticalSubnode A C)
            (centeredSubnode (centeredSubnode (.cellNode h A B C D)))))
          (hashLifeStepRecursiveAux fuel (makeCellNode (centeredHorizontalSubnode A B)
            (centeredSubnode B) (centeredSubnode (centeredSubnode (.cellNode h A B C D)))
            (centeredVerticalSubnode B D)))
          (hashLifeStepRecursiveAux fuel (makeCellNode (centeredVerticalSubnode A C)
            (centeredSubnode (centeredSubnode (.cellNode h A B C D))) (centeredSubnode C)
            (centeredHorizontalSubnode C D)))
          (hashLifeStepRecursiveAux fuel (makeCellNode
            (centeredSubnode (centeredSubnode (.cellNode h A B C D)))
            (centeredVerticalSubnode B D) (centeredHorizontalSubnode C D) (centeredSubnode D))) := by
      subst hA' hB' hC' hD'
      rfl
    rw [hstep]
    -- Widths in terms of the eighth-width `e = 2^(K-3)`.
    obtain ⟨e, hev⟩ : ∃ e, (2 : ℤ) ^ (K - 3) = e := ⟨_, rfl⟩
    have he : (2 : ℤ) ^ (K - 1 - 2) = e := by rw [show K - 1 - 2 = K - 3 by omega, hev]
    have he1 : 1 ≤ e := by rw [← hev]; exact pow_two_pos _
    obtain ⟨hK11, hK1⟩ := pow_two_sub_two (L := K - 1) (by omega) he
    have hK2 : (2 : ℤ) ^ (K - 2) = 2 * e := by rw [← hK11, show K - 1 - 1 = K - 2 by omega]
    rw [show K - 1 = K - 1 - 1 + 1 by omega] at hK1
    rw [show K - 1 - 1 + 1 = K - 1 by omega] at hK1
    have hM := cellAt_cellNode_width (h := h) (ne := B) (sw := C) (se := D) hA (by omega) hK1
    generalize hMv : cellAt (.cellNode h A B C D) = M at hM
    -- The nine overlapping subnodes.
    obtain ⟨w00, s00⟩ := cs_spec hA (by omega) (by omega) he
    obtain ⟨w01, s01⟩ := chs_spec hA hB (by omega) (by omega) he
    obtain ⟨w02, s02⟩ := cs_spec hB (by omega) (by omega) he
    obtain ⟨w10, s10⟩ := cvs_spec hA hC (by omega) (by omega) he
    obtain ⟨wm, sm⟩ := cs_spec hm h5 hK hK2
    obtain ⟨w11, s11⟩ := cs_spec wm (by omega) (by omega) he
    obtain ⟨w12, s12⟩ := cvs_spec hB hD (by omega) (by omega) he
    obtain ⟨w20, s20⟩ := cs_spec hC (by omega) (by omega) he
    obtain ⟨w21, s21⟩ := chs_spec hC hD (by omega) (by omega) he
    obtain ⟨w22, s22⟩ := cs_spec hD (by omega) (by omega) he
    rw [hMv] at sm
    have p00 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredSubnode A) x y = M (x + e) (y + e) := by
      intro x y hx0 hx hy0 hy
      rw [s00 x y hx0 hx hy0 hy, hM]
      quad_descend
    have p01 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredHorizontalSubnode A B) x y = M (x + 3 * e) (y + e) := by
      intro x y hx0 hx hy0 hy
      rw [s01 (cellAt C) (cellAt D) x y hx0 hx hy0 hy, hM]
    have p02 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredSubnode B) x y = M (x + 5 * e) (y + e) := by
      intro x y hx0 hx hy0 hy
      rw [s02 x y hx0 hx hy0 hy, hM]
      quad_descend
      coord_congr
    have p10 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredVerticalSubnode A C) x y = M (x + e) (y + 3 * e) := by
      intro x y hx0 hx hy0 hy
      rw [s10 (cellAt B) (cellAt D) x y hx0 hx hy0 hy, hM]
    have p11 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredSubSubnode (.cellNode h A B C D)) x y = M (x + 3 * e) (y + 3 * e) := by
      intro x y hx0 hx hy0 hy
      unfold centeredSubSubnode
      rw [s11 x y hx0 hx hy0 hy, sm _ _ (by omega) (by omega) (by omega) (by omega)]
      coord_congr
    have p12 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredVerticalSubnode B D) x y = M (x + 5 * e) (y + 3 * e) := by
      intro x y hx0 hx hy0 hy
      rw [s12 (fun _ _ => false) (fun _ _ => false) x y hx0 hx hy0 hy, hM,
        show x + 5 * e = (x + e) + 2 * (2 * e) by omega,
        quadSel_shift_right _ _ _ _ (fun _ _ => false) (fun _ _ => false) _ _ _ (by omega) (by omega)]
    have p20 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredSubnode C) x y = M (x + e) (y + 5 * e) := by
      intro x y hx0 hx hy0 hy
      rw [s20 x y hx0 hx hy0 hy, hM]
      quad_descend
      coord_congr
    have p21 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredHorizontalSubnode C D) x y = M (x + 3 * e) (y + 5 * e) := by
      intro x y hx0 hx hy0 hy
      rw [s21 (fun _ _ => false) (fun _ _ => false) x y hx0 hx hy0 hy, hM,
        show y + 5 * e = (y + e) + 2 * (2 * e) by omega,
        quadSel_shift_down _ _ _ _ (fun _ _ => false) (fun _ _ => false) _ _ _ (by omega) (by omega)]
    have p22 : ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
        cellAt (centeredSubnode D) x y = M (x + 5 * e) (y + 5 * e) := by
      intro x y hx0 hx hy0 hy
      rw [s22 x y hx0 hx hy0 hy, hM]
      quad_descend
      coord_congr
    -- The four overlapping quadrants of level K - 1.
    have hd : K - 1 - 1 < 2 ^ 32 := by omega
    have quad : ∀ {P1 P2 P3 P4 : MacroCell} (ox oy : ℤ), WFd P1 (K - 1 - 1) → WFd P2 (K - 1 - 1) →
        WFd P3 (K - 1 - 1) → WFd P4 (K - 1 - 1) →
        (∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e → cellAt P1 x y = M (x + ox) (y + oy)) →
        (∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
          cellAt P2 x y = M (x + (ox + 2 * e)) (y + oy)) →
        (∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
          cellAt P3 x y = M (x + ox) (y + (oy + 2 * e))) →
        (∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
          cellAt P4 x y = M (x + (ox + 2 * e)) (y + (oy + 2 * e))) →
        WFd (makeCellNode P1 P2 P3 P4) (K - 1) ∧
        ∀ x y, 0 ≤ x → x < 2 * (2 * e) → 0 ≤ y → y < 2 * (2 * e) →
          cellAt (makeCellNode P1 P2 P3 P4) x y = M (x + ox) (y + oy) := by
      intro P1 P2 P3 P4 ox oy h1 h2 h3 h4 q1 q2 q3 q4
      have hw := WFd_makeCellNode h1 h2 h3 h4
      rw [show K - 1 - 1 + 1 = K - 1 by omega] at hw
      refine ⟨hw, fun x y hx0 hx hy0 hy => ?_⟩
      rw [cellAt_makeCellNode_width h1 hd hK11]
      exact quadrant_of_pieces _ _ _ _ M e ox oy q1 q2 q3 q4 x y hx0 hx hy0 hy
    obtain ⟨wq1, hq1⟩ := quad e e w00 w01 w10 w11 p00 (piece_retarget p01 (by omega) rfl)
      (piece_retarget p10 rfl (by omega)) (piece_retarget p11 (by omega) (by omega))
    obtain ⟨wq2, hq2⟩ := quad (3 * e) e w01 w02 w11 w12 p01 (piece_retarget p02 (by omega) rfl)
      (piece_retarget p11 rfl (by omega)) (piece_retarget p12 (by omega) (by omega))
    obtain ⟨wq3, hq3⟩ := quad e (3 * e) w10 w11 w20 w21 p10 (piece_retarget p11 (by omega) rfl)
      (piece_retarget p20 rfl (by omega)) (piece_retarget p21 (by omega) (by omega))
    obtain ⟨wq4, hq4⟩ := quad (3 * e) (3 * e) w11 w12 w21 w22 p11
      (piece_retarget p12 (by omega) rfl) (piece_retarget p21 rfl (by omega))
      (piece_retarget p22 (by omega) (by omega))
    -- Recursively step each quadrant.
    have recStep : ∀ {q : MacroCell}, WFd q (K - 1) →
        WFd (hashLifeStepRecursiveAux fuel q) (K - 1 - 1) ∧
        ∀ x y, 0 ≤ x → x < 2 * e → 0 ≤ y → y < 2 * e →
          cellAt (hashLifeStepRecursiveAux fuel q) x y = nextGenAt (cellAt q) (x + e) (y + e) := by
      intro q hq
      obtain ⟨hw, hs⟩ := hashLifeStepRecursiveAux_spec fuel hq (by omega) (by omega) (by omega)
      refine ⟨hw, fun x y hx0 hx hy0 hy => ?_⟩
      rw [hs x y hx0 (by rw [hK11]; exact hx) hy0 (by rw [hK11]; exact hy), he]
    obtain ⟨wr1, hr1⟩ := recStep wq1
    obtain ⟨wr2, hr2⟩ := recStep wq2
    obtain ⟨wr3, hr3⟩ := recStep wq3
    obtain ⟨wr4, hr4⟩ := recStep wq4
    have hw := WFd_makeCellNode wr1 wr2 wr3 wr4
    rw [show K - 1 - 1 + 1 = K - 1 by omega] at hw
    refine ⟨hw, fun x y hx0 hx hy0 hy => ?_⟩
    rw [cellAt_makeCellNode_width wr1 hd hK11, hK2]
    rw [show K - 1 = K - 1 - 1 + 1 by omega, pow_two_pred (K - 1 - 1 + 1) (by omega),
      show K - 1 - 1 + 1 - 1 = K - 1 - 1 by omega, hK11] at hx hy
    exact step_assembly M _ _ _ _ _ _ _ _ e he1 hq1 hq2 hq3 hq4 hr1 hr2 hr3 hr4 x y hx0 hx hy0 hy

-- =========================================================================
-- Expansion Semantics
-- =========================================================================

/-- The everywhere-dead cell function. -/
def deadFn : ℤ → ℤ → Bool := fun _ _ => false

theorem quadSel_dead (w : ℤ) : quadSel deadFn deadFn deadFn deadFn w = deadFn := by
  funext x y
  unfold quadSel deadFn
  repeat' split
  all_goals rfl

theorem leafAt_zero_fun : leafAt 0 = deadFn := by
  funext x y
  exact leafAt_zero x y

theorem cellAt_makeLevel4Node_fun (nw ne sw se : UInt64) :
    cellAt (makeLevel4Node nw ne sw se) = quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 := by
  funext x y
  rfl

theorem cellAt_emptyLevel4 : cellAt emptyLevel4 = deadFn := by
  rw [show emptyLevel4 = makeLevel4Node 0 0 0 0 from rfl]
  funext x y
  rw [cellAt_makeLevel4Node, leafAt_zero_fun, quadSel_dead]

theorem emptySubnode_spec : ∀ {n : MacroCell} {d : ℕ}, WFd n d →
    WFd (emptySubnode n) d ∧ cellAt (emptySubnode n) = deadFn
  | .level4Node .., d, h => by
    rw [WFd_level4Node_iff] at h
    subst h
    exact ⟨rfl, cellAt_emptyLevel4⟩
  | .cellNode _ nw _ _ _, d, h => by
    rw [WFd_cellNode_iff] at h
    obtain ⟨h5, h1, _, _, _⟩ := h
    obtain ⟨w, c⟩ := emptySubnode_spec h1
    have hw := WFd_makeCellNode w w w w
    rw [show d - 1 + 1 = d by omega] at hw
    refine ⟨hw, ?_⟩
    funext x y
    change cellAt (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)
      (emptySubnode nw)) x y = _
    rw [cellAt_makeCellNode, c, quadSel_dead]

theorem quadSel_true_cases {f1 f2 f3 f4 : ℤ → ℤ → Bool} {w x y : ℤ}
    (h : quadSel f1 f2 f3 f4 w x y = true) :
    (0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < w ∧ f1 x y = true) ∨
    (w ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < w ∧ f2 (x - w) y = true) ∨
    (0 ≤ x ∧ x < w ∧ w ≤ y ∧ y < 2 * w ∧ f3 x (y - w) = true) ∨
    (w ≤ x ∧ x < 2 * w ∧ w ≤ y ∧ y < 2 * w ∧ f4 (x - w) (y - w) = true) := by
  have hb := quadSel_bounds h
  by_cases hxw : x < w <;> by_cases hyw : y < w
  · rw [quadSel_nw _ _ _ _ _ _ _ hb.1 hxw hb.2.2.1 hyw] at h
    exact Or.inl ⟨hb.1, hxw, hb.2.2.1, hyw, h⟩
  · rw [quadSel_sw _ _ _ _ _ _ _ hb.1 hxw (by omega) hb.2.2.2] at h
    exact Or.inr (Or.inr (Or.inl ⟨hb.1, hxw, by omega, hb.2.2.2, h⟩))
  · rw [quadSel_ne _ _ _ _ _ _ _ (by omega) hb.2.1 hb.2.2.1 hyw] at h
    exact Or.inr (Or.inl ⟨by omega, hb.2.1, hb.2.2.1, hyw, h⟩)
  · rw [quadSel_se _ _ _ _ _ _ _ (by omega) hb.2.1 (by omega) hb.2.2.2] at h
    exact Or.inr (Or.inr (Or.inr ⟨by omega, hb.2.1, by omega, hb.2.2.2, h⟩))

/-- Case-splits a `quadSel _ = true` hypothesis, discarding dead quadrants. -/
macro "peel_true " h:ident : tactic =>
  `(tactic| first
    | (simp only [deadFn, Bool.false_eq_true] at $h:ident; done)
    | rcases quadSel_true_cases $h with ⟨_, _, _, _, $h:ident⟩ | ⟨_, _, _, _, $h:ident⟩ |
        ⟨_, _, _, _, $h:ident⟩ | ⟨_, _, _, _, $h:ident⟩)

/-- Closes `f a b = true` from `h : f a' b' = true` when the coordinates agree arithmetically. -/
macro "coord_exact " h:ident : tactic =>
  `(tactic| (refine (fn_congr2 _ ?_ ?_).trans $h <;> omega))

/--
Surrounding a quadtree with dead space: the original occupies the window offset by `3w`.
-/
theorem quadSel_expand (fa fb fc fd : ℤ → ℤ → Bool) (w : ℤ) (_hw : 0 < w) (x y : ℤ) :
    quadSel
      (quadSel deadFn deadFn deadFn (quadSel deadFn deadFn deadFn fa w) (2 * w))
      (quadSel deadFn deadFn (quadSel deadFn deadFn fb deadFn w) deadFn (2 * w))
      (quadSel deadFn (quadSel deadFn fc deadFn deadFn w) deadFn deadFn (2 * w))
      (quadSel (quadSel fd deadFn deadFn deadFn w) deadFn deadFn deadFn (2 * w))
      (2 * (2 * w)) x y =
    quadSel fa fb fc fd w (x - 3 * w) (y - 3 * w) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    peel_true h <;> peel_true h <;> peel_true h
    all_goals try (simp only [deadFn, Bool.false_eq_true] at h; done)
    all_goals
      quad_descend
      coord_exact h
  · intro h
    peel_true h
    all_goals
      quad_descend
      coord_exact h

theorem expandCentered_spec {m : MacroCell} {K : ℕ} (hm : WFd m K) (hK : K + 2 < 2 ^ 32) :
    WFd (expandCentered m) (K + 2) ∧
    ∀ x y, cellAt (expandCentered m) x y =
      cellAt m (x - 3 * 2 ^ (K - 1)) (y - 3 * 2 ^ (K - 1)) := by
  cases m with
  | level4Node h a b c d =>
    rw [WFd_level4Node_iff] at hm
    subst hm
    have e4 : WFd emptyLevel4 4 := rfl
    have q1 : WFd (makeCellNode emptyLevel4 emptyLevel4 emptyLevel4 (makeLevel4Node 0 0 0 a)) 5 :=
      WFd_makeCellNode e4 e4 e4 (WFd_makeLevel4Node _ _ _ _)
    have q2 : WFd (makeCellNode emptyLevel4 emptyLevel4 (makeLevel4Node 0 0 b 0) emptyLevel4) 5 :=
      WFd_makeCellNode e4 e4 (WFd_makeLevel4Node _ _ _ _) e4
    have q3 : WFd (makeCellNode emptyLevel4 (makeLevel4Node 0 c 0 0) emptyLevel4 emptyLevel4) 5 :=
      WFd_makeCellNode e4 (WFd_makeLevel4Node _ _ _ _) e4 e4
    have q4 : WFd (makeCellNode (makeLevel4Node d 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4) 5 :=
      WFd_makeCellNode (WFd_makeLevel4Node _ _ _ _) e4 e4 e4
    refine ⟨WFd_makeCellNode q1 q2 q3 q4, ?_⟩
    intro x y
    change cellAt (makeCellNode
      (makeCellNode emptyLevel4 emptyLevel4 emptyLevel4 (makeLevel4Node 0 0 0 a))
      (makeCellNode emptyLevel4 emptyLevel4 (makeLevel4Node 0 0 b 0) emptyLevel4)
      (makeCellNode emptyLevel4 (makeLevel4Node 0 c 0 0) emptyLevel4 emptyLevel4)
      (makeCellNode (makeLevel4Node d 0 0 0) emptyLevel4 emptyLevel4 emptyLevel4)) x y = _
    rw [cellAt_makeCellNode_width q1 (by omega) (show (2 : ℤ) ^ 5 = 2 * (2 * 8) by decide),
      cellAt_makeCellNode_width e4 (by omega) (show (2 : ℤ) ^ 4 = 2 * 8 by decide),
      cellAt_makeCellNode_width e4 (by omega) (show (2 : ℤ) ^ 4 = 2 * 8 by decide),
      cellAt_makeCellNode_width e4 (by omega) (show (2 : ℤ) ^ 4 = 2 * 8 by decide),
      cellAt_makeCellNode_width (WFd_makeLevel4Node d 0 0 0) (by omega)
        (show (2 : ℤ) ^ 4 = 2 * 8 by decide),
      cellAt_emptyLevel4, cellAt_level4Node_fun,
      show (2 : ℤ) ^ (4 - 1) = 8 by decide]
    simp only [cellAt_makeLevel4Node_fun, leafAt_zero_fun]
    exact quadSel_expand _ _ _ _ 8 (by decide) x y
  | cellNode h nw ne sw se =>
    have hm' := hm
    rw [WFd_cellNode_iff] at hm'
    obtain ⟨h5, h1, h2, h3, h4⟩ := hm'
    obtain ⟨we, ce⟩ := emptySubnode_spec h1
    have l1 : WFd (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) nw) K := by
      have := WFd_makeCellNode we we we h1; rwa [show K - 1 + 1 = K by omega] at this
    have l2 : WFd (makeCellNode (emptySubnode nw) (emptySubnode nw) ne (emptySubnode nw)) K := by
      have := WFd_makeCellNode we we h2 we; rwa [show K - 1 + 1 = K by omega] at this
    have l3 : WFd (makeCellNode (emptySubnode nw) sw (emptySubnode nw) (emptySubnode nw)) K := by
      have := WFd_makeCellNode we h3 we we; rwa [show K - 1 + 1 = K by omega] at this
    have l4 : WFd (makeCellNode se (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)) K := by
      have := WFd_makeCellNode h4 we we we; rwa [show K - 1 + 1 = K by omega] at this
    have l0 : WFd (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)
        (emptySubnode nw)) K := by
      have := WFd_makeCellNode we we we we; rwa [show K - 1 + 1 = K by omega] at this
    refine ⟨WFd_makeCellNode (WFd_makeCellNode l0 l0 l0 l1) (WFd_makeCellNode l0 l0 l2 l0)
      (WFd_makeCellNode l0 l3 l0 l0) (WFd_makeCellNode l4 l0 l0 l0), ?_⟩
    intro x y
    have p1 : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := pow_two_pred K (by omega)
    have p2 : (2 : ℤ) ^ (K + 1) = 2 * (2 * 2 ^ (K - 1)) := by
      rw [show K + 1 = (K + 1 - 1) + 1 by omega, Int.pow_succ', show K + 1 - 1 = K by omega, p1]
    have ce1 : cellAt (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)
        (emptySubnode nw)) = deadFn := by
      funext x y; rw [cellAt_makeCellNode, ce, quadSel_dead]
    change cellAt (makeCellNode
      (makeCellNode (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) nw))
      (makeCellNode (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) ne (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)))
      (makeCellNode (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) sw (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)))
      (makeCellNode (makeCellNode se (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw))
        (makeCellNode (emptySubnode nw) (emptySubnode nw) (emptySubnode nw) (emptySubnode nw)))) x y = _
    have hw0 := WFd_makeCellNode l0 l0 l0 l1
    rw [cellAt_makeCellNode_width hw0 (by omega) p2, cellAt_makeCellNode_width l0 (by omega) p1,
      cellAt_makeCellNode_width l0 (by omega) p1, cellAt_makeCellNode_width l0 (by omega) p1,
      cellAt_makeCellNode_width l4 (by omega) p1, ce1,
      cellAt_makeCellNode_width we (by omega) rfl, cellAt_makeCellNode_width we (by omega) rfl,
      cellAt_makeCellNode_width we (by omega) rfl, cellAt_makeCellNode_width h4 (by omega) rfl, ce,
      cellAt_cellNode_width h1 (by omega) rfl]
    exact quadSel_expand _ _ _ _ _ (pow_two_pos _) x y

end Algorithm

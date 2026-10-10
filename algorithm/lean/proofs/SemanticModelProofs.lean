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
import proofs.GridEquivalenceProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Quadrant Selection
-- =========================================================================

theorem quadSel_nw (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < w) (hy0 : 0 ≤ y) (hy : y < w) :
    quadSel f1 f2 f3 f4 w x y = f1 x y := by
  unfold quadSel
  rw [ite_eq_left (by omega), ite_eq_left hx, ite_eq_left hy]

theorem quadSel_ne (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ)
    (hx0 : w ≤ x) (hx : x < 2 * w) (hy0 : 0 ≤ y) (hy : y < w) :
    quadSel f1 f2 f3 f4 w x y = f2 (x - w) y := by
  unfold quadSel
  rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left hy]

theorem quadSel_sw (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < w) (hy0 : w ≤ y) (hy : y < 2 * w) :
    quadSel f1 f2 f3 f4 w x y = f3 x (y - w) := by
  unfold quadSel
  rw [ite_eq_left (by omega), ite_eq_left hx, ite_eq_right (by omega)]

theorem quadSel_se (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ)
    (hx0 : w ≤ x) (hx : x < 2 * w) (hy0 : w ≤ y) (hy : y < 2 * w) :
    quadSel f1 f2 f3 f4 w x y = f4 (x - w) (y - w) := by
  unfold quadSel
  rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem quadSel_out (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ)
    (h : ¬ (0 ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < 2 * w)) :
    quadSel f1 f2 f3 f4 w x y = false := by
  unfold quadSel
  rw [ite_eq_right h]

theorem quadSel_bounds {f1 f2 f3 f4 : ℤ → ℤ → Bool} {w x y : ℤ}
    (h : quadSel f1 f2 f3 f4 w x y = true) :
    0 ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < 2 * w := by
  unfold quadSel at h
  split at h
  · assumption
  · cases h

/--
Assembly of a cell function from four quadrants that each agree with a target function.
-/
theorem quadSel_eq_of_quadrants (f1 f2 f3 f4 T : ℤ → ℤ → Bool) (w : ℤ)
    (h1 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → f1 x y = T x y)
    (h2 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → f2 x y = T (x + w) y)
    (h3 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → f3 x y = T x (y + w))
    (h4 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → f4 x y = T (x + w) (y + w))
    (x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * w) (hy0 : 0 ≤ y) (hy : y < 2 * w) :
    quadSel f1 f2 f3 f4 w x y = T x y := by
  by_cases hxw : x < w <;> by_cases hyw : y < w
  · rw [quadSel_nw _ _ _ _ _ _ _ hx0 hxw hy0 hyw, h1 x y hx0 hxw hy0 hyw]
  · rw [quadSel_sw _ _ _ _ _ _ _ hx0 hxw (by omega) hy, h3 x (y - w) hx0 hxw (by omega) (by omega)]
    rw [Int.sub_add_cancel]
  · rw [quadSel_ne _ _ _ _ _ _ _ (by omega) hx hy0 hyw, h2 (x - w) y (by omega) (by omega) hy0 hyw]
    rw [Int.sub_add_cancel]
  · rw [quadSel_se _ _ _ _ _ _ _ (by omega) hx (by omega) hy,
      h4 (x - w) (y - w) (by omega) (by omega) (by omega) (by omega)]
    rw [Int.sub_add_cancel, Int.sub_add_cancel]

-- =========================================================================
-- cellAt Unfolding
-- =========================================================================

theorem cellAt_level4Node (h : UInt32) (nw ne sw se : UInt64) (x y : ℤ) :
    cellAt (.level4Node h nw ne sw se) x y =
    quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 x y := rfl

theorem cellAt_cellNode (h : UInt32) (nw ne sw se : MacroCell) (x y : ℤ) :
    cellAt (.cellNode h nw ne sw se) x y =
    quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) ((2 : ℤ) ^ nw.level.toNat) x y := rfl

theorem cellAt_makeLevel4Node (nw ne sw se : UInt64) (x y : ℤ) :
    cellAt (makeLevel4Node nw ne sw se) x y =
    quadSel (leafAt nw) (leafAt ne) (leafAt sw) (leafAt se) 8 x y := rfl

theorem cellAt_makeCellNode (nw ne sw se : MacroCell) (x y : ℤ) :
    cellAt (makeCellNode nw ne sw se) x y =
    quadSel (cellAt nw) (cellAt ne) (cellAt sw) (cellAt se) ((2 : ℤ) ^ nw.level.toNat) x y := rfl

theorem leafAt_bounds {leaf : UInt64} {x y : ℤ} (h : leafAt leaf x y = true) :
    0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 := by
  unfold leafAt at h
  split at h
  · assumption
  · cases h

theorem leafAt_zero (x y : ℤ) : leafAt 0 x y = false := by
  unfold leafAt
  split <;> simp

-- =========================================================================
-- Depth-Indexed Well-Formedness
-- =========================================================================

theorem WFd_level4Node_iff (h : UInt32) (nw ne sw se : UInt64) (d : ℕ) :
    WFd (.level4Node h nw ne sw se) d ↔ d = 4 := Iff.rfl

theorem WFd_cellNode_iff (h : UInt32) (nw ne sw se : MacroCell) (d : ℕ) :
    WFd (.cellNode h nw ne sw se) d ↔
    5 ≤ d ∧ WFd nw (d - 1) ∧ WFd ne (d - 1) ∧ WFd sw (d - 1) ∧ WFd se (d - 1) := Iff.rfl

theorem WFd_ge_four : ∀ {m : MacroCell} {d : ℕ}, WFd m d → 4 ≤ d
  | .level4Node .., _, h => by rw [WFd_level4Node_iff] at h; omega
  | .cellNode .., _, h => by rw [WFd_cellNode_iff] at h; omega

theorem WFd_depth : ∀ {m : MacroCell} {d : ℕ}, WFd m d → m.depth = d
  | .level4Node .., _, h => by rw [WFd_level4Node_iff] at h; subst h; rfl
  | .cellNode _ nw _ _ _, _, h => by
    rw [WFd_cellNode_iff] at h
    have := WFd_depth h.2.1
    show nw.depth + 1 = _
    omega

theorem WFd_level_toNat : ∀ {m : MacroCell} {d : ℕ}, WFd m d → d < 2 ^ 32 → m.level.toNat = d
  | .level4Node .., _, h, _ => by rw [WFd_level4Node_iff] at h; subst h; rfl
  | .cellNode _ nw _ _ _, d, h, hd => by
    rw [WFd_cellNode_iff] at h
    have ih := WFd_level_toNat h.2.1 (by omega)
    show (nw.level + 1).toNat = d
    rw [UInt32.toNat_add, ih]
    simp only [UInt32.reduceToNat]
    omega

theorem WFd_level4 {m : MacroCell} (h : WFd m 4) :
    ∃ hh nw ne sw se, m = .level4Node hh nw ne sw se := by
  cases m with
  | level4Node hh nw ne sw se => exact ⟨hh, nw, ne, sw, se, rfl⟩
  | cellNode => rw [WFd_cellNode_iff] at h; omega

theorem WFd_cell {m : MacroCell} {d : ℕ} (h : WFd m d) (hd : 5 ≤ d) :
    ∃ hh nw ne sw se, m = .cellNode hh nw ne sw se ∧
      WFd nw (d - 1) ∧ WFd ne (d - 1) ∧ WFd sw (d - 1) ∧ WFd se (d - 1) := by
  cases m with
  | level4Node => rw [WFd_level4Node_iff] at h; omega
  | cellNode hh nw ne sw se =>
    rw [WFd_cellNode_iff] at h
    exact ⟨hh, nw, ne, sw, se, rfl, h.2⟩

theorem WFd_makeCellNode {nw ne sw se : MacroCell} {d : ℕ}
    (h1 : WFd nw d) (h2 : WFd ne d) (h3 : WFd sw d) (h4 : WFd se d) :
    WFd (makeCellNode nw ne sw se) (d + 1) := by
  have := WFd_ge_four h1
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> simpa

theorem WFd_makeLevel4Node (nw ne sw se : UInt64) : WFd (makeLevel4Node nw ne sw se) 4 := rfl

theorem isWellFormed_of_WFd : ∀ {m : MacroCell} {d : ℕ}, WFd m d → isWellFormed m
  | .level4Node .., _, _ => trivial
  | .cellNode _ nw ne sw se, _, h => by
    rw [WFd_cellNode_iff] at h
    obtain ⟨_, h1, h2, h3, h4⟩ := h
    refine ⟨isWellFormed_of_WFd h1, isWellFormed_of_WFd h2, isWellFormed_of_WFd h3,
      isWellFormed_of_WFd h4, ?_, ?_, ?_⟩
    all_goals
      first
      | rw [WFd_depth h1, WFd_depth h2]
      | rw [WFd_depth h2, WFd_depth h3]
      | rw [WFd_depth h3, WFd_depth h4]

theorem WFd_of_isWellFormed : ∀ {m : MacroCell}, isWellFormed m → WFd m m.depth
  | .level4Node .., _ => rfl
  | .cellNode _ nw ne sw se, h => by
    obtain ⟨h1, h2, h3, h4, e1, e2, e3⟩ := h
    have w1 := WFd_of_isWellFormed h1
    have w2 := WFd_of_isWellFormed h2
    have w3 := WFd_of_isWellFormed h3
    have w4 := WFd_of_isWellFormed h4
    have hge := WFd_ge_four w1
    show 5 ≤ nw.depth + 1 ∧ WFd nw (nw.depth + 1 - 1) ∧ WFd ne (nw.depth + 1 - 1) ∧
      WFd sw (nw.depth + 1 - 1) ∧ WFd se (nw.depth + 1 - 1)
    simp only [Nat.add_sub_cancel]
    refine ⟨by omega, w1, ?_, ?_, ?_⟩
    · rw [e1]; exact w2
    · rw [e1, e2]; exact w3
    · rw [e1, e2, e3]; exact w4

theorem cellAt_bounds {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d < 2 ^ 32) {x y : ℤ}
    (h : cellAt m x y = true) :
    0 ≤ x ∧ x < (2 : ℤ) ^ d ∧ 0 ≤ y ∧ y < (2 : ℤ) ^ d := by
  cases m with
  | level4Node =>
    rw [WFd_level4Node_iff] at hm
    subst hm
    exact quadSel_bounds h
  | cellNode _ nw ne sw se =>
    rw [WFd_cellNode_iff] at hm
    rw [cellAt_cellNode, WFd_level_toNat hm.2.1 (by omega)] at h
    have hb := quadSel_bounds h
    have hp : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := by
      rw [← Int.pow_succ']
      congr 1
      omega
    rw [hp]
    exact hb

-- =========================================================================
-- Leaf Bit Layout
-- =========================================================================

def mortonX (b : ℕ) : ℕ := b % 2 + 2 * (b / 4 % 2) + 4 * (b / 16 % 2)

def mortonY (b : ℕ) : ℕ := b / 2 % 2 + 2 * (b / 8 % 2) + 4 * (b / 32 % 2)

theorem bitToCoord8x8_morton : ∀ b < 64,
    bitToCoord8x8 b = some ((mortonX b : ℤ), (mortonY b : ℤ)) ∧
    mortonIndex (mortonX b) (mortonY b) = b ∧ mortonX b < 8 ∧ mortonY b < 8 := by
  decide

theorem mortonIndex_inverse : ∀ x < 8, ∀ y < 8,
    mortonIndex x y < 64 ∧ mortonX (mortonIndex x y) = x ∧ mortonY (mortonIndex x y) = y := by
  decide

theorem shiftRight_eq_div (a k : ℕ) : shiftRight a k = a / 2 ^ k := by
  induction k generalizing a with
  | zero => simp [shiftRight]
  | succ k ih =>
    rw [shiftRight, ih, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]

theorem testBit_eq_nat_testBit (n i : ℕ) : testBit n i = n.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, testBit, shiftRight_eq_div]
  cases h : n / 2 ^ i % 2 == 1 <;> simp_all

theorem uint64_testBit_eq_getLsbD (l : UInt64) (i : ℕ) :
    testBit l.toNat i = l.toBitVec.getLsbD i := by
  rw [testBit_eq_nat_testBit]
  rfl

theorem mem_leafToGrid_iff (ox oy : ℤ) (leaf : UInt64) (c : Coord) :
    c ∈ leafToGrid ox oy leaf ↔ leafAt leaf (c.1 - ox) (c.2 - oy) = true := by
  unfold leafToGrid
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, hf⟩
    rw [List.mem_range] at hb
    obtain ⟨hcoord, hidx, hx8, hy8⟩ := bitToCoord8x8_morton b hb
    split at hf
    · rename_i htest
      rw [hcoord] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      unfold leafAt
      have e1 : ox + (mortonX b : ℤ) - ox = (mortonX b : ℤ) := by omega
      have e2 : oy + (mortonY b : ℤ) - oy = (mortonY b : ℤ) := by omega
      simp only [e1, e2]
      rw [ite_eq_left (by omega)]
      simp only [Int.toNat_natCast, hidx]
      rw [← uint64_testBit_eq_getLsbD]
      exact htest
    · cases hf
  · intro h
    have hb := leafAt_bounds h
    unfold leafAt at h
    rw [ite_eq_left hb] at h
    obtain ⟨hlt, hmx, hmy⟩ := mortonIndex_inverse (c.1 - ox).toNat (by omega) (c.2 - oy).toNat (by omega)
    refine ⟨mortonIndex (c.1 - ox).toNat (c.2 - oy).toNat, List.mem_range.mpr hlt, ?_⟩
    rw [uint64_testBit_eq_getLsbD, h, ite_eq_left rfl]
    obtain ⟨hcoord, _, _, _⟩ := bitToCoord8x8_morton _ hlt
    rw [hcoord, hmx, hmy]
    simp only [Option.some.injEq]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ext <;> simp <;> omega

-- =========================================================================
-- Grid Membership Correspondence
-- =========================================================================

/-- A cell function is dead outside of [0, w) x [0, w). -/
def Supp (f : ℤ → ℤ → Bool) (w : ℤ) : Prop :=
  ∀ x y, f x y = true → 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < w

theorem quadSel_eq_true_iff {f1 f2 f3 f4 : ℤ → ℤ → Bool} {w : ℤ}
    (h1 : Supp f1 w) (h2 : Supp f2 w) (h3 : Supp f3 w) (h4 : Supp f4 w) (x y : ℤ) :
    quadSel f1 f2 f3 f4 w x y = true ↔
    (f1 x y = true ∨ f2 (x - w) y = true ∨ f3 x (y - w) = true ∨ f4 (x - w) (y - w) = true) := by
  constructor
  · intro h
    have hb := quadSel_bounds h
    by_cases hxw : x < w <;> by_cases hyw : y < w
    · rw [quadSel_nw _ _ _ _ _ _ _ hb.1 hxw hb.2.2.1 hyw] at h; exact Or.inl h
    · rw [quadSel_sw _ _ _ _ _ _ _ hb.1 hxw (by omega) hb.2.2.2] at h; exact Or.inr (Or.inr (Or.inl h))
    · rw [quadSel_ne _ _ _ _ _ _ _ (by omega) hb.2.1 hb.2.2.1 hyw] at h; exact Or.inr (Or.inl h)
    · rw [quadSel_se _ _ _ _ _ _ _ (by omega) hb.2.1 (by omega) hb.2.2.2] at h
      exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · have := h1 _ _ h
      rw [quadSel_nw _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact h
    · have := h2 _ _ h
      rw [quadSel_ne _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact h
    · have := h3 _ _ h
      rw [quadSel_sw _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact h
    · have := h4 _ _ h
      rw [quadSel_se _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]; exact h

theorem leafAt_supp (leaf : UInt64) : Supp (leafAt leaf) 8 :=
  fun _ _ h => leafAt_bounds h

theorem cellAt_supp {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d < 2 ^ 32) :
    Supp (cellAt m) ((2 : ℤ) ^ d) :=
  fun _ _ h => cellAt_bounds hm hd h

theorem mem_macroCellToGrid_iff : ∀ {m : MacroCell} {d : ℕ}, WFd m d → d < 2 ^ 32 →
    ∀ (ox oy : ℤ) (c : Coord),
    c ∈ macroCellToGrid ox oy m ↔ cellAt m (c.1 - ox) (c.2 - oy) = true
  | .level4Node _ nw ne sw se, _, _, _, ox, oy, c => by
    rw [cellAt_level4Node, quadSel_eq_true_iff (leafAt_supp _) (leafAt_supp _) (leafAt_supp _)
      (leafAt_supp _)]
    simp only [macroCellToGrid, List.mem_append, mem_leafToGrid_iff, Int.sub_sub, or_assoc]
  | .cellNode _ nw ne sw se, d, hm, hd, ox, oy, c => by
    have hm' := (WFd_cellNode_iff _ _ _ _ _ _).mp hm
    obtain ⟨_, h1, h2, h3, h4⟩ := hm'
    rw [cellAt_cellNode, WFd_level_toNat h1 (by omega),
      quadSel_eq_true_iff (cellAt_supp h1 (by omega)) (cellAt_supp h2 (by omega))
        (cellAt_supp h3 (by omega)) (cellAt_supp h4 (by omega))]
    simp only [macroCellToGrid, WFd_level_toNat h1 (by omega), List.mem_append,
      mem_macroCellToGrid_iff h1 (by omega), mem_macroCellToGrid_iff h2 (by omega),
      mem_macroCellToGrid_iff h3 (by omega), mem_macroCellToGrid_iff h4 (by omega), Int.sub_sub,
      or_assoc]

-- =========================================================================
-- Conway Stepping on Cell Functions
-- =========================================================================

theorem countAliveNeighbors_of_cellFn (L : List Coord) (g : ℤ → ℤ → Bool)
    (hL : ∀ c, c ∈ L ↔ g c.1 c.2 = true) (c : Coord) :
    countAliveNeighbors c L = neighborCountAt g c.1 c.2 := by
  unfold countAliveNeighbors neighborCountAt mooreNeighbors
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro d _
  simp only [Function.comp]
  rw [Bool.eq_iff_iff, List.contains_iff_mem, hL]

theorem mem_stepGrid_iff_nextGenAt (L : List Coord) (g : ℤ → ℤ → Bool)
    (hL : ∀ c, c ∈ L ↔ g c.1 c.2 = true) (c : Coord) :
    c ∈ stepGrid L ↔ nextGenAt g c.1 c.2 = true := by
  have hD : ∀ c, c ∈ deduplicate L ↔ g c.1 c.2 = true := by
    intro c
    rw [mem_deduplicate_iff, hL]
  rw [mem_stepGrid_iff, countAliveNeighbors_of_cellFn _ g hD]
  unfold nextGenAt
  have hc : (deduplicate L).contains c = g c.1 c.2 := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, hD]
  rw [hc]

theorem neighborCountAt_eq (f : ℤ → ℤ → Bool) (x y : ℤ) :
    neighborCountAt f x y =
    (f (x - 1) (y - 1)).toNat + (f x (y - 1)).toNat + (f (x + 1) (y - 1)).toNat +
    (f (x - 1) y).toNat + (f (x + 1) y).toNat +
    (f (x - 1) (y + 1)).toNat + (f x (y + 1)).toNat + (f (x + 1) (y + 1)).toNat := by
  unfold neighborCountAt mooreOffsets
  simp only [List.filter_cons, List.filter_nil]
  have e1 : x + -1 = x - 1 := by omega
  have e2 : y + -1 = y - 1 := by omega
  simp only [e1, e2, Int.add_zero]
  cases f (x - 1) (y - 1) <;> cases f x (y - 1) <;> cases f (x + 1) (y - 1) <;>
    cases f (x - 1) y <;> cases f (x + 1) y <;> cases f (x - 1) (y + 1) <;>
    cases f x (y + 1) <;> cases f (x + 1) (y + 1) <;> rfl

/--
Locality of Conway's rule: the next state of a cell depends only on its 3x3 neighborhood.
-/
theorem nextGenAt_congr (f g : ℤ → ℤ → Bool) (x y x' y' : ℤ)
    (h : ∀ dx dy, -1 ≤ dx → dx ≤ 1 → -1 ≤ dy → dy ≤ 1 → f (x + dx) (y + dy) = g (x' + dx) (y' + dy)) :
    nextGenAt f x y = nextGenAt g x' y' := by
  unfold nextGenAt
  rw [neighborCountAt_eq, neighborCountAt_eq]
  have hc := h 0 0 (by omega) (by omega) (by omega) (by omega)
  have h1 := h (-1) (-1) (by omega) (by omega) (by omega) (by omega)
  have h2 := h 0 (-1) (by omega) (by omega) (by omega) (by omega)
  have h3 := h 1 (-1) (by omega) (by omega) (by omega) (by omega)
  have h4 := h (-1) 0 (by omega) (by omega) (by omega) (by omega)
  have h5 := h 1 0 (by omega) (by omega) (by omega) (by omega)
  have h6 := h (-1) 1 (by omega) (by omega) (by omega) (by omega)
  have h7 := h 0 1 (by omega) (by omega) (by omega) (by omega)
  have h8 := h 1 1 (by omega) (by omega) (by omega) (by omega)
  simp only [Int.add_zero, ← Int.sub_eq_add_neg] at hc h1 h2 h3 h4 h5 h6 h7 h8
  rw [hc, h1, h2, h3, h4, h5, h6, h7, h8]

theorem nextGenAt_dead_of_isolated (f : ℤ → ℤ → Bool) (x y : ℤ)
    (h : ∀ dx dy, -1 ≤ dx → dx ≤ 1 → -1 ≤ dy → dy ≤ 1 → f (x + dx) (y + dy) = false) :
    nextGenAt f x y = false := by
  have := nextGenAt_congr f (fun _ _ => false) x y 0 0 (fun dx dy a b c d => h dx dy a b c d)
  rw [this]
  rfl

end Algorithm

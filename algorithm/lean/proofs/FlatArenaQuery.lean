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

import Algorithm.MacroCell
import Algorithm.HashLife
import Algorithm.HashLifeEquivalence
import Algorithm.FlatHashLife
import AlgorithmDefs
import proofs.SemanticModelProofs
import proofs.HashLifeStepProofs
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern
import proofs.FlatArenaGeneration

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: cell queries

`containsCell` reads exactly the cells of the MacroCell a node denotes, at every level.
-/

-- =========================================================================
-- Leaves
-- =========================================================================

theorem cellToLeafBit_table : ∀ x y : Fin 8,
    cellToLeafBitUInt x.val.toUInt32 y.val.toUInt32 = (mortonIndex x.val y.val).toUInt32 := by
  decide

theorem u64_shift_and_one (l s : UInt64) (hs : s.toNat < 64) :
    (((l >>> s) &&& 1) == 1) = l.toBitVec.getLsbD s.toNat := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hs, UInt64.toNat_one, Nat.and_one_is_mod, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  simp

theorem i64_toUInt32_eq {v : Int64} (h0 : 0 ≤ v.toInt) : v.toUInt64.toUInt32 = v.toInt.toNat.toUInt32 := by
  have e := Int64.toNat_toUInt64_of_le (x := v) (Int64.le_iff_toInt_le.mpr (by simpa using h0))
  apply UInt32.toNat.inj
  rw [UInt64.toNat_toUInt32, e, show v.toNatClampNeg = v.toInt.toNat from rfl, Nat.toUInt32, UInt32.toNat_ofNat']

theorem mortonIndex_lt {x y : ℕ} (hx : x < 8) (hy : y < 8) : mortonIndex x y < 64 := by
  unfold mortonIndex
  omega

theorem leafContains_eq (l : UInt64) {v w : Int64} (hv0 : 0 ≤ v.toInt) (hv : v.toInt < 8) (hw0 : 0 ≤ w.toInt)
    (hw : w.toInt < 8) : leafContains l v.toUInt64.toUInt32 w.toUInt64.toUInt32 = leafAt l v.toInt w.toInt := by
  rw [i64_toUInt32_eq hv0, i64_toUInt32_eq hw0]
  have hx : v.toInt.toNat < 8 := by omega
  have hy : w.toInt.toNat < 8 := by omega
  have ht := cellToLeafBit_table ⟨_, hx⟩ ⟨_, hy⟩
  dsimp only at ht
  have hm := mortonIndex_lt hx hy
  have hs : ((mortonIndex v.toInt.toNat w.toInt.toNat).toUInt32.toUInt64).toNat =
      mortonIndex v.toInt.toNat w.toInt.toNat := by
    rw [UInt32.toNat_toUInt64, u32_ofNat_toNat (by omega)]
  unfold leafContains leafAt
  dsimp only
  rw [ht, u64_shift_and_one _ _ (by rw [hs]; exact hm), hs, ite_eq_left (by omega)]

-- =========================================================================
-- Quadrant selection in 64-bit coordinates
-- =========================================================================

theorem i64_sub_toInt {x y : Int64} (h1 : -2 ^ 63 ≤ x.toInt - y.toInt) (h2 : x.toInt - y.toInt < 2 ^ 63) :
    (x - y).toInt = x.toInt - y.toInt := by
  rw [Int64.toInt_sub, bmod64_small h1 h2]

theorem i64_zero_toInt : (0 : Int64).toInt = 0 := by decide

theorem i64_eight_toInt : (8 : Int64).toInt = 8 := by decide

theorem quadSel_split (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w x y : ℤ) (hx0 : 0 ≤ x) (hx : x < 2 * w)
    (hy0 : 0 ≤ y) (hy : y < 2 * w) (e s : Bool) (he : e = true ↔ w ≤ x) (hs : s = true ↔ w ≤ y) :
    quadSel f1 f2 f3 f4 w x y =
      (if s = true then (if e = true then f4 else f3) else (if e = true then f2 else f1))
        (if e = true then x - w else x) (if s = true then y - w else y) := by
  cases e <;> cases s <;> simp only [Bool.false_eq_true, false_iff, true_iff, ↓reduceIte] at he hs ⊢
  · exact quadSel_nw _ _ _ _ _ _ _ hx0 (by omega) hy0 (by omega)
  · exact quadSel_sw _ _ _ _ _ _ _ hx0 (by omega) hs hy
  · exact quadSel_ne _ _ _ _ _ _ _ he hx hy0 (by omega)
  · exact quadSel_se _ _ _ _ _ _ _ he hx hs hy

theorem containsRange_iff {L : UInt32} {h : ℕ} (hL : L.toNat = h + 5) (rx ry : Int64) :
    (rx < 0 || ry < 0 || (L < 63 && (rx >= pow2Int64 L || ry >= pow2Int64 L))) = true ↔
      ¬ (0 ≤ rx.toInt ∧ rx.toInt < 2 * 2 ^ (h + 4) ∧ 0 ≤ ry.toInt ∧ ry.toInt < 2 * 2 ^ (h + 4)) := by
  have h2 : (2 : ℤ) * 2 ^ (h + 4) = 2 ^ (h + 5) := by
    rw [pow_two_pred (h + 5) (by omega), show h + 5 - 1 = h + 4 by omega]
  rw [h2]
  have hx := Int64.toInt_lt rx
  have hy := Int64.toInt_lt ry
  have h63 : (63 : UInt32).toNat = 63 := rfl
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Int64.lt_iff_toInt_lt, ge_iff_le,
    Int64.le_iff_toInt_le, i64_zero_toInt, u32_lt_iff, h63, hL]
  by_cases hs : h + 5 < 63
  · rw [pow2Int64_toInt (by omega), hL]
    omega
  · have hb := pow_two_le_pow (show 63 ≤ h + 5 by omega)
    omega

theorem containsHalf {L : UInt32} {h : ℕ} (hL : L.toNat = h + 5) {rx : Int64} (h0 : 0 ≤ rx.toInt) :
    ((L <= 63 && rx >= pow2Int64 (L - 1)) = true ↔ 2 ^ (h + 4) ≤ rx.toInt) ∧
    ((L <= 63 && rx >= pow2Int64 (L - 1)) = true → (rx - pow2Int64 (L - 1)).toInt = rx.toInt - 2 ^ (h + 4)) := by
  have hL1 : (L - 1).toNat = h + 4 := by
    rw [u32_toNat_sub (by simp; omega), hL]
    simp
  have hx := Int64.toInt_lt rx
  have h63 : (63 : UInt32).toNat = 63 := rfl
  by_cases hs : h + 5 ≤ 63
  · have hp : (pow2Int64 (L - 1)).toInt = 2 ^ (h + 4) := by rw [pow2Int64_toInt (by omega), hL1]
    have hb := pow_two_le_pow (show h + 4 ≤ 62 by omega)
    have hpos := pow_two_pos' (h + 4)
    have h62 : (2 : ℤ) ^ 62 < 2 ^ 63 := by decide
    have hL63 : L ≤ 63 := by rw [u32_le_iff, h63]; omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, Int64.le_iff_toInt_le, hp, hL63, true_and]
    intro hge
    rw [i64_sub_toInt (by rw [hp]; omega) (by rw [hp]; omega), hp]
  · have hL63 : ¬ L ≤ 63 := by rw [u32_le_iff, h63]; omega
    have hb := pow_two_le_pow (show 63 ≤ h + 4 by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq, hL63, false_and, false_implies, and_true, false_iff,
      Int.not_le]
    omega

-- =========================================================================
-- containsCell
-- =========================================================================

theorem containsLevel4_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {c : UInt32} {M : MacroCell}
    (hc : NodeIs a 0 c M) {rx ry : Int64} (hx0 : 0 ≤ rx.toInt) (hx : rx.toInt < 2 * 8) (hy0 : 0 ≤ ry.toInt)
    (hy : ry.toInt < 2 * 8) : containsLevel4 a c rx ry = cellAt M rx.toInt ry.toInt := by
  unfold containsLevel4
  by_cases h0 : c = 0
  · subst h0
    rw [ite_eq_left (by simp), ← hc.2, (NodeIs.emptyL4 hwf).2, cellAt_emptyLevel4]
    rfl
  · have hlt := hc.1
    rw [ite_eq_right (by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, h0, false_or, ge_iff_le, u32_le_iff]
      have := u32_lt_iff.mp hlt
      omega)]
    rw [← hc.2, denoteLevel4_of_lt hlt, cellAt_makeLevel4Node]
    dsimp only
    have he8 : (decide (rx ≥ 8) = true ↔ 8 ≤ rx.toInt) := by
      simp [Int64.le_iff_toInt_le, i64_eight_toInt]
    have hs8 : (decide (ry ≥ 8) = true ↔ 8 ≤ ry.toInt) := by
      simp [Int64.le_iff_toInt_le, i64_eight_toInt]
    rw [quadSel_split _ _ _ _ _ _ _ hx0 hx hy0 hy _ _ he8 hs8]
    have hsx : 8 ≤ rx.toInt → (rx - 8).toInt = rx.toInt - 8 := fun h => by
      rw [i64_sub_toInt (by rw [i64_eight_toInt]; omega) (by rw [i64_eight_toInt]; have := Int64.toInt_lt rx; omega),
        i64_eight_toInt]
    have hsy : 8 ≤ ry.toInt → (ry - 8).toInt = ry.toInt - 8 := fun h => by
      rw [i64_sub_toInt (by rw [i64_eight_toInt]; omega) (by rw [i64_eight_toInt]; have := Int64.toInt_lt ry; omega),
        i64_eight_toInt]
    have hx8 : rx ≥ 8 ↔ 8 ≤ rx.toInt := by rw [ge_iff_le, Int64.le_iff_toInt_le, i64_eight_toInt]
    have hy8 : ry ≥ 8 ↔ 8 ≤ ry.toInt := by rw [ge_iff_le, Int64.le_iff_toInt_le, i64_eight_toInt]
    by_cases hE : rx ≥ 8 <;> by_cases hS : ry ≥ 8 <;>
      simp only [hE, hS, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    · have h1 := hx8.mp hE
      have h2 := hy8.mp hS
      rw [← hsx h1, ← hsy h2]
      exact leafContains_eq _ (by rw [hsx h1]; omega) (by rw [hsx h1]; omega) (by rw [hsy h2]; omega)
        (by rw [hsy h2]; omega)
    · have h1 := hx8.mp hE
      have h2 := mt hy8.mpr hS
      rw [← hsx h1]
      exact leafContains_eq _ (by rw [hsx h1]; omega) (by rw [hsx h1]; omega) hy0 (by omega)
    · have h1 := mt hx8.mpr hE
      have h2 := hy8.mp hS
      rw [← hsy h2]
      exact leafContains_eq _ hx0 (by omega) (by rw [hsy h2]; omega) (by rw [hsy h2]; omega)
    · have h1 := mt hx8.mpr hE
      have h2 := mt hy8.mpr hS
      exact leafContains_eq _ hx0 (by omega) hy0 (by omega)

/--
`containsCellLoop` on a node of height `h + 1` with at least `h + 1` fuel reads exactly the cells of the
MacroCell the node denotes.
-/
theorem containsCellLoop_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) :
    ∀ (h : ℕ) {id : UInt32} {m : MacroCell}, NodeIs a (h + 1) id m → ∀ (rx ry : Int64) (fuel : UInt32),
      h + 1 ≤ fuel.toNat → a.containsCellLoop id rx ry fuel = cellAt m rx.toInt ry.toInt
  | h, id, m, hn, rx, ry, fuel, hf => by
    have hf0 : fuel ≠ 0 := fun h0 => by subst h0; simp at hf
    obtain ⟨c1, c2, c3, c4, hM⟩ := hn.children hwf
    have hL : (a.cellLevel[id.toNat]!).toUInt32.toNat = h + 5 := by
      rw [u8_toUInt32_toNat]
      exact hn.level
    have hw : (denoteAt h a a.cellNw[id.toNat]!).level.toNat = h + 4 :=
      WFd_level_toNat c1.WFd (by have := u32_toNat_lt (a.cellLevel[id.toNat]!).toUInt32; omega)
    rw [hM, cellAt_makeCellNode, hw]
    rw [FlatHashLifeArena.containsCellLoop, dite_eq_right hf0]
    rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hn.lt_cell; omega)]
    dsimp only
    generalize (a.cellLevel[id.toNat]!).toUInt32 = L at hL ⊢
    by_cases hr : (rx < 0 || ry < 0 || (L < 63 && (rx >= pow2Int64 L || ry >= pow2Int64 L))) = true
    · rw [ite_eq_left hr, quadSel_out _ _ _ _ _ _ _ ((containsRange_iff hL rx ry).mp hr)]
    · rw [ite_eq_right hr]
      obtain ⟨hx0, hx, hy0, hy⟩ := Classical.not_not.mp (mt (containsRange_iff hL rx ry).mpr hr)
      obtain ⟨he, hex⟩ := containsHalf hL hx0
      obtain ⟨hs, hsy⟩ := containsHalf hL hy0
      rw [quadSel_split _ _ _ _ _ _ _ hx0 hx hy0 hy _ _ he hs]
      have h5 : (5 : UInt32).toNat = 5 := rfl
      have step : ∀ (c : UInt32) (rx' ry' : Int64), NodeIs a h c (denoteAt h a c) →
          0 ≤ rx'.toInt → rx'.toInt < 2 ^ (h + 4) → 0 ≤ ry'.toInt → ry'.toInt < 2 ^ (h + 4) →
          (if L ≤ 5 then containsLevel4 a c rx' ry' else a.containsCellLoop c rx' ry' (fuel - 1)) =
            cellAt (denoteAt h a c) rx'.toInt ry'.toInt := by
        intro c rx' ry' hc h1 h2 h3 h4
        cases h with
        | zero =>
          rw [ite_eq_left (by rw [u32_le_iff]; omega)]
          have e16 : (2 : ℤ) ^ (0 + 4) = 16 := by decide
          exact containsLevel4_spec hwf hc h1 (by omega) h3 (by omega)
        | succ j =>
          rw [ite_eq_right (by rw [u32_le_iff]; omega)]
          have hf1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_toNat_sub (by simp; omega)
          exact containsCellLoop_spec hwf j hc rx' ry' (fuel - 1) (by omega)
      have hpos := pow_two_pos' (h + 4)
      cases hE : (decide (L ≤ 63) && decide (rx ≥ pow2Int64 (L - 1))) <;>
        cases hS : (decide (L ≤ 63) && decide (ry ≥ pow2Int64 (L - 1))) <;>
        rw [hE] at he hex <;> rw [hS] at hs hsy <;>
        simp only [Bool.false_eq_true, false_iff, true_iff, ↓reduceIte, Int.not_le] at he hs ⊢
      · exact step _ rx ry c1 hx0 he hy0 hs
      · rw [← hsy rfl]
        exact step _ rx _ c3 hx0 he (by rw [hsy rfl]; omega) (by rw [hsy rfl]; omega)
      · rw [← hex rfl]
        exact step _ _ ry c2 (by rw [hex rfl]; omega) (by rw [hex rfl]; omega) hy0 hs
      · rw [← hex rfl, ← hsy rfl]
        exact step _ _ _ c4 (by rw [hex rfl]; omega) (by rw [hex rfl]; omega) (by rw [hsy rfl]; omega)
          (by rw [hsy rfl]; omega)

/--
`containsCell` on a CellNode reads exactly the cells of the MacroCell it denotes.
-/
theorem containsCell_spec {a : FlatHashLifeArena} (hwf : ArenaWF a) {id : UInt32} (hid : id < a.cellCount)
    (rx ry : Int64) : a.containsCell id rx ry = cellAt (denoteCell a id) rx.toInt ry.toInt := by
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' hwf hid
  unfold FlatHashLifeArena.containsCell
  rw [hn.denoteCell_eq]
  have := u8_toNat_lt (a.cellLevel[id.toNat]!)
  unfold cellLevelOf at hk
  exact containsCellLoop_spec hwf k hn rx ry 256 (by simp; omega)

/--
For any root of a well-formed arena with top-left corner `(ox, oy)`, `containsCell` at the offset of `(x, y)`
(computed exactly in 64 bits) is `true` exactly when `(x, y)` is a live cell of the state.
-/
theorem containsCell_grid {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (ox oy x y : Int32) :
    a.containsCell root (x.toInt64 - ox.toInt64) (y.toInt64 - oy.toInt64) = true ↔
      (x.toInt, y.toInt) ∈ hashLifeToGrid (flatState a ox oy root) := by
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' hwf hid
  have hW := hn.WFd
  have := u8_toNat_lt (a.cellLevel[root.toNat]!)
  unfold cellLevelOf at hk
  rw [containsCell_spec hwf hid]
  unfold hashLifeToGrid flatState
  dsimp only
  rw [mem_macroCellToGrid_iff hW (by omega)]
  have hx1 := Int32.toInt_lt x
  have hx2 := Int32.le_toInt x
  have hy1 := Int32.toInt_lt y
  have hy2 := Int32.le_toInt y
  have ho1 := Int32.toInt_lt ox
  have ho2 := Int32.le_toInt ox
  have hp1 := Int32.toInt_lt oy
  have hp2 := Int32.le_toInt oy
  have h31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
  have h63 : (2 : ℤ) ^ 63 = 9223372036854775808 := by decide
  rw [i64_sub_toInt (by rw [Int32.toInt_toInt64, Int32.toInt_toInt64]; omega)
      (by rw [Int32.toInt_toInt64, Int32.toInt_toInt64]; omega),
    i64_sub_toInt (by rw [Int32.toInt_toInt64, Int32.toInt_toInt64]; omega)
      (by rw [Int32.toInt_toInt64, Int32.toInt_toInt64]; omega),
    Int32.toInt_toInt64, Int32.toInt_toInt64, Int32.toInt_toInt64, Int32.toInt_toInt64]

end Algorithm

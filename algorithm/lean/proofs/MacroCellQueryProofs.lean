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

import proofs.MacroCellEngineProofs
import proofs.FlatArenaBasics
import proofs.MacroCellProofs

/-!
# MacroCell cell queries

The cell queries that Kotlin calls on a `MacroCell` (`leafContains`, `macroCellContains`, `leafWithCell`,
`macroCellWithCell`, `cellToLeafBitUInt`, `minimumMacroCellLevel`) agree with the cell function `cellAt` at every
`Int32` coordinate.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

theorem cellToLeafBit_morton : ∀ a < 8, ∀ b < 8, (cellToLeafBitUInt a.toUInt32 b.toUInt32).toNat = mortonIndex a b := by
  decide +kernel

theorem shr_and_one_eq_one (w k : UInt64) (hk : k.toNat < 64) :
    ((w >>> k) &&& 1 == 1) = w.toBitVec.getLsbD k.toNat := by
  have key : (w >>> k) &&& 1 = if w.toBitVec.getLsbD k.toNat then 1 else 0 := by
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      split <;> simp_all [BitVec.ushiftRight_eq', Nat.mod_eq_of_lt hk]
    · split <;> simp [BitVec.getLsbD_and, h0, BitVec.getLsbD_one]
  rw [key]
  split <;> simp_all

theorem leafContains_toNat (leaf : UInt64) (x y : UInt32) (hx : x.toNat < 8) (hy : y.toNat < 8) :
    leafContains leaf x y = leafAt leaf x.toNat y.toNat := by
  have hb := cellToLeafBit_morton x.toNat hx y.toNat hy
  simp only [UInt32.ofNat_toNat] at hb
  unfold leafContains leafAt
  have hlt : (cellToLeafBitUInt x y).toUInt64.toNat < 64 := by simp [hb]; unfold mortonIndex; omega
  rw [shr_and_one_eq_one _ _ hlt]
  simp [hb]
  intro _
  exact ⟨by omega, by omega⟩

theorem int32_shl_one : ∀ L < 31, ((1 : Int32) <<< L.toUInt32.toInt32).toInt = 2 ^ L := by decide +kernel

theorem int32_shl_one_pred : ∀ L < 31, 1 ≤ L → ((1 : Int32) <<< (L.toUInt32.toInt32 - 1)).toInt = 2 ^ (L - 1) := by
  decide +kernel

theorem int32_toInt_sub_of_range (a b : Int32) (h1 : -2 ^ 31 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub, Int.bmod_eq_emod]
  split <;> omega


theorem int32_toUInt32_toNat (x : Int32) (h : 0 ≤ x.toInt) : ((x.toUInt32.toNat : ℕ) : ℤ) = x.toInt := by
  rw [Int32.toNat_toUInt32_of_le (Int32.le_iff_toInt_le.mpr (by simpa using h))]
  simp only [Int32.toNatClampNeg]
  omega

theorem leafContains_int32 (leaf : UInt64) (x y : Int32) (hx0 : 0 ≤ x.toInt) (hx : x.toInt < 8) (hy0 : 0 ≤ y.toInt)
    (hy : y.toInt < 8) : leafContains leaf x.toUInt32 y.toUInt32 = leafAt leaf x.toInt y.toInt := by
  have ex := int32_toUInt32_toNat x hx0
  have ey := int32_toUInt32_toNat y hy0
  rw [leafContains_toNat _ _ _ (by omega) (by omega), ex, ey]

/-- The Kotlin `contains` query of a MacroCell is its cell function, at every `Int32` coordinate. -/
theorem macroCellContains_correct : ∀ (m : MacroCell) {d : ℕ}, WFd m d → d ≤ 30 → ∀ x y : Int32,
    macroCellContains m x y = cellAt m x.toInt y.toInt := by
  intro m
  induction m with
  | level4Node h nw ne sw se =>
    intro d hm hd x y
    rw [WFd_level4Node_iff] at hm
    subst hm
    rw [macroCellContains, cellAt_level4Node, show (MacroCell.level4Node h nw ne sw se).level = 4 from rfl]
    have hw : ((1 : Int32) <<< (4 : UInt32).toInt32).toInt = 16 := by decide
    have hh : ((1 : Int32) <<< ((4 : UInt32).toInt32 - 1)).toInt = 8 := by decide
    generalize (1 : Int32) <<< (4 : UInt32).toInt32 = W at hw ⊢
    generalize (1 : Int32) <<< ((4 : UInt32).toInt32 - 1) = Hh at hh ⊢
    have hxl := x.toInt_lt; have hxg := x.le_toInt
    have hyl := y.toInt_lt; have hyg := y.le_toInt
    by_cases hin : 0 ≤ x.toInt ∧ x.toInt < 16 ∧ 0 ≤ y.toInt ∧ y.toInt < 16
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le,
          hw, Int32.toInt_zero]
        omega
      simp only [c, Bool.false_eq_true, ↓reduceIte]
      by_cases hx8 : x.toInt < 8 <;> by_cases hy8 : y.toInt < 8
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true]
        rw [leafContains_int32 _ _ _ (by omega) hx8 (by omega) hy8, quadSel_nw _ _ _ _ _ _ _ (by omega) hx8 (by omega) hy8]
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true, decide_false]
        rw [quadSel_sw _ _ _ _ _ _ _ (by omega) hx8 (by omega) (by omega)]
        have e := int32_toInt_sub_of_range y Hh (by omega) (by omega)
        rw [leafContains_int32 _ _ _ (by omega) hx8 (by omega) (by omega), e, hh]
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true, decide_false]
        rw [quadSel_ne _ _ _ _ _ _ _ (by omega) (by omega) (by omega) hy8]
        have e := int32_toInt_sub_of_range x Hh (by omega) (by omega)
        rw [leafContains_int32 _ _ _ (by omega) (by omega) (by omega) hy8, e, hh]
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_false]
        rw [quadSel_se _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]
        have e1 := int32_toInt_sub_of_range x Hh (by omega) (by omega)
        have e2 := int32_toInt_sub_of_range y Hh (by omega) (by omega)
        rw [leafContains_int32 _ _ _ (by omega) (by omega) (by omega) (by omega), e1, e2, hh]
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hw,
          Int32.toInt_zero]
        omega
      simp only [c, ↓reduceIte]
      rw [quadSel_out _ _ _ _ _ _ _ (by omega)]
  | cellNode h nw ne sw se ih1 ih2 ih3 ih4 =>
    intro d hm hd x y
    obtain ⟨h5, h1, h2, h3, h4⟩ := hm
    rw [macroCellContains, cellAt_cellNode, WFd_level_toNat h1 (by omega)]
    have hlev := level_eq_of_WFd (m := .cellNode h nw ne sw se) ⟨h5, h1, h2, h3, h4⟩ (by omega)
    have hw := int32_shl_one d (by omega)
    have hh := int32_shl_one_pred d (by omega) (by omega)
    rw [hlev]
    generalize (1 : Int32) <<< d.toUInt32.toInt32 = W at hw ⊢
    generalize (1 : Int32) <<< (d.toUInt32.toInt32 - 1) = Hh at hh ⊢
    have hp : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := pow_two_pred d (by omega)
    have hp30 := pow_two_le_pow_two_30 (d - 1) (by omega)
    have hpos := pow_two_pos (d - 1)
    have h30 : (2 : ℤ) ^ 30 = 1073741824 := by decide
    have hxl := x.toInt_lt; have hxg := x.le_toInt
    have hyl := y.toInt_lt; have hyg := y.le_toInt
    by_cases hin : 0 ≤ x.toInt ∧ x.toInt < 2 * 2 ^ (d - 1) ∧ 0 ≤ y.toInt ∧ y.toInt < 2 * 2 ^ (d - 1)
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le,
          hw, Int32.toInt_zero]
        omega
      simp only [c, Bool.false_eq_true, ↓reduceIte]
      by_cases hxh : x.toInt < 2 ^ (d - 1) <;> by_cases hyh : y.toInt < 2 ^ (d - 1)
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true]
        rw [ih1 h1 (by omega), quadSel_nw _ _ _ _ _ _ _ (by omega) hxh (by omega) hyh]
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true, decide_false]
        rw [ih3 h3 (by omega), quadSel_sw _ _ _ _ _ _ _ (by omega) hxh (by omega) (by omega),
          int32_toInt_sub_of_range y Hh (by omega) (by omega), hh]
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true, decide_false]
        rw [ih2 h2 (by omega), quadSel_ne _ _ _ _ _ _ _ (by omega) (by omega) (by omega) hyh,
          int32_toInt_sub_of_range x Hh (by omega) (by omega), hh]
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_false]
        rw [ih4 h4 (by omega), quadSel_se _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega),
          int32_toInt_sub_of_range x Hh (by omega) (by omega), int32_toInt_sub_of_range y Hh (by omega) (by omega),
          hh]
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hw,
          Int32.toInt_zero]
        omega
      simp only [c, ↓reduceIte]
      rw [quadSel_out _ _ _ _ _ _ _ (by omega)]


theorem mortonIndex_inj {a b a' b' : ℕ} (ha : a < 8) (hb : b < 8) (ha' : a' < 8) (hb' : b' < 8)
    (h : mortonIndex a b = mortonIndex a' b') : a = a' ∧ b = b' := by
  obtain ⟨_, h1, h2⟩ := mortonIndex_inverse a ha b hb
  obtain ⟨_, h1', h2'⟩ := mortonIndex_inverse a' ha' b' hb'
  rw [h] at h1 h2
  exact ⟨h1.symm.trans h1', h2.symm.trans h2'⟩

theorem mortonIndex_lt_64 : ∀ a < 8, ∀ b < 8, mortonIndex a b < 64 := by decide +kernel

theorem u64_not_getLsbD (x : UInt64) (i : ℕ) : (~~~x).toBitVec.getLsbD i = (decide (i < 64) && !x.toBitVec.getLsbD i) := by
  simp [BitVec.getLsbD_not]

theorem getLsbD_one_shl (k : UInt64) (hk : k.toNat < 64) (i : ℕ) :
    ((1 : UInt64) <<< k).toBitVec.getLsbD i = (decide (i < 64) && decide (i = k.toNat)) := by
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.toNat_umod,
    UInt64.toNat_toBitVec]
  rw [Nat.mod_eq_of_lt (by simpa using hk)]
  by_cases h : i = k.toNat
  · subst h; simp
  · by_cases hlt : i < k.toNat
    · simp [hlt, h]
    · simp only [hlt, decide_false, Bool.not_false, Bool.and_true, h, Bool.and_false]
      rw [show (1 : UInt64).toBitVec = 1#64 from rfl, BitVec.getLsbD_one]
      simp; omega

/-- Setting a cell of a leaf changes exactly that cell. -/
theorem leafAt_leafWithCell (leaf : UInt64) (x y : UInt32) (hx : x.toNat < 8) (hy : y.toNat < 8) (b : Bool)
    (x' y' : ℤ) :
    leafAt (leafWithCell leaf x y b) x' y' =
      if x' = x.toNat ∧ y' = y.toNat then b else leafAt leaf x' y' := by
  have hb := cellToLeafBit_morton x.toNat hx y.toNat hy
  simp only [UInt32.ofNat_toNat] at hb
  have hlt : (cellToLeafBitUInt x y).toUInt64.toNat < 64 := by
    simp only [UInt32.toNat_toUInt64, hb]; exact mortonIndex_lt_64 _ hx _ hy
  have hbit : (cellToLeafBitUInt x y).toUInt64.toNat = mortonIndex x.toNat y.toNat := by
    simp only [UInt32.toNat_toUInt64, hb]
  unfold leafWithCell leafAt
  by_cases hin : 0 ≤ x' ∧ x' < 8 ∧ 0 ≤ y' ∧ y' < 8
  · have hm0 := mortonIndex_lt_64 _ hx _ hy
    by_cases heq : x' = x.toNat ∧ y' = y.toNat
    · obtain ⟨rfl, rfl⟩ := heq
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toBitVec_or, UInt64.toBitVec_and, BitVec.getLsbD_or, BitVec.getLsbD_and, u64_not_getLsbD,
        getLsbD_one_shl _ hlt, hbit] <;>
        simp [hin, hm0]
    · have hm1 := mortonIndex_lt_64 x'.toNat (by omega) y'.toNat (by omega)
      have hne : mortonIndex x'.toNat y'.toNat ≠ mortonIndex x.toNat y.toNat := by
        intro he
        have := mortonIndex_inj (by omega) (by omega) hx hy he
        omega
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toBitVec_or, UInt64.toBitVec_and, BitVec.getLsbD_or, BitVec.getLsbD_and, u64_not_getLsbD,
        getLsbD_one_shl _ hlt, hbit] <;>
        simp [hin, heq, hne, hm1]
  · have hne : ¬ (x' = x.toNat ∧ y' = y.toNat) := by omega
    simp [hin, hne]

/-- Updating one cell of one quadrant of a `quadSel` updates that cell of the whole. -/
theorem quadSel_update (f1 f2 f3 f4 g1 g2 g3 g4 : ℤ → ℤ → Bool) (w a c : ℤ) (b : Bool)
    (ha : 0 ≤ a ∧ a < 2 * w) (hc : 0 ≤ c ∧ c < 2 * w)
    (h1 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → g1 x y = if x = a ∧ y = c then b else f1 x y)
    (h2 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → g2 x y = if x + w = a ∧ y = c then b else f2 x y)
    (h3 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → g3 x y = if x = a ∧ y + w = c then b else f3 x y)
    (h4 : ∀ x y, 0 ≤ x → x < w → 0 ≤ y → y < w → g4 x y = if x + w = a ∧ y + w = c then b else f4 x y)
    (x y : ℤ) :
    quadSel g1 g2 g3 g4 w x y = if x = a ∧ y = c then b else quadSel f1 f2 f3 f4 w x y := by
  unfold quadSel
  by_cases hin : 0 ≤ x ∧ x < 2 * w ∧ 0 ≤ y ∧ y < 2 * w
  · simp only [hin, and_self, ↓reduceIte]
    by_cases hx : x < w <;> by_cases hy : y < w <;> simp only [hx, hy, ↓reduceIte]
    · rw [h1 x y (by omega) hx (by omega) hy]
    · rw [h3 x (y - w) (by omega) hx (by omega) (by omega), Int.sub_add_cancel]
    · rw [h2 (x - w) y (by omega) (by omega) (by omega) hy, Int.sub_add_cancel]
    · rw [h4 (x - w) (y - w) (by omega) (by omega) (by omega) (by omega), Int.sub_add_cancel, Int.sub_add_cancel]
  · have : ¬(x = a ∧ y = c) := by omega
    simp only [hin, this, ↓reduceIte]


theorem ite_neg' {c : Prop} [Decidable c] (h : ¬c) {α : Sort _} (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem ite_pos' {c : Prop} [Decidable c] (h : c) {α : Sort _} (a b : α) : (if c then a else b) = a := by
  simp [h]

/-- The cell function after `macroCellWithCell m x y b`: `(x, y)` set to `b` if it is inside the node. -/
def updatedAt (f : ℤ → ℤ → Bool) (a c : ℤ) (b : Bool) (x y : ℤ) : Bool :=
  if x = a ∧ y = c then b else f x y

theorem quadSel_update_nw (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w a c : ℤ) (b : Bool) (ha : 0 ≤ a ∧ a < w)
    (hc : 0 ≤ c ∧ c < w) (x y : ℤ) :
    quadSel (updatedAt f1 a c b) f2 f3 f4 w x y = updatedAt (quadSel f1 f2 f3 f4 w) a c b x y :=
  quadSel_update f1 f2 f3 f4 _ _ _ _ w a c b ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)])
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) x y

theorem quadSel_update_ne (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w a c : ℤ) (b : Bool) (ha : w ≤ a ∧ a < 2 * w)
    (hc : 0 ≤ c ∧ c < w) (x y : ℤ) :
    quadSel f1 (updatedAt f2 (a - w) c b) f3 f4 w x y = updatedAt (quadSel f1 f2 f3 f4 w) a c b x y :=
  quadSel_update f1 f2 f3 f4 _ _ _ _ w a c b ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)])
    (fun x' y' _ _ _ _ => by
      unfold updatedAt
      by_cases e : x' = a - w ∧ y' = c
      · rw [ite_pos' e, ite_pos' (by omega)]
      · rw [ite_neg' e, ite_neg' (by omega)])
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) x y

theorem quadSel_update_sw (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w a c : ℤ) (b : Bool) (ha : 0 ≤ a ∧ a < w)
    (hc : w ≤ c ∧ c < 2 * w) (x y : ℤ) :
    quadSel f1 f2 (updatedAt f3 a (c - w) b) f4 w x y = updatedAt (quadSel f1 f2 f3 f4 w) a c b x y :=
  quadSel_update f1 f2 f3 f4 _ _ _ _ w a c b ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)])
    (fun x' y' _ _ _ _ => by
      unfold updatedAt
      by_cases e : x' = a ∧ y' = c - w
      · rw [ite_pos' e, ite_pos' (by omega)]
      · rw [ite_neg' e, ite_neg' (by omega)])
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) x y

theorem quadSel_update_se (f1 f2 f3 f4 : ℤ → ℤ → Bool) (w a c : ℤ) (b : Bool) (ha : w ≤ a ∧ a < 2 * w)
    (hc : w ≤ c ∧ c < 2 * w) (x y : ℤ) :
    quadSel f1 f2 f3 (updatedAt f4 (a - w) (c - w) b) w x y = updatedAt (quadSel f1 f2 f3 f4 w) a c b x y :=
  quadSel_update f1 f2 f3 f4 _ _ _ _ w a c b ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)]) (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)])
    (fun _ _ _ _ _ _ => by rw [ite_neg' (by omega)])
    (fun x' y' _ _ _ _ => by
      unfold updatedAt
      by_cases e : x' = a - w ∧ y' = c - w
      · rw [ite_pos' e, ite_pos' (by omega)]
      · rw [ite_neg' e, ite_neg' (by omega)]) x y

theorem leafAt_leafWithCell_int32 (leaf : UInt64) (x y : Int32) (hx0 : 0 ≤ x.toInt) (hx : x.toInt < 8)
    (hy0 : 0 ≤ y.toInt) (hy : y.toInt < 8) (b : Bool) (x' y' : ℤ) :
    leafAt (leafWithCell leaf x.toUInt32 y.toUInt32 b) x' y' = updatedAt (leafAt leaf) x.toInt y.toInt b x' y' := by
  have ex := int32_toUInt32_toNat x hx0
  have ey := int32_toUInt32_toNat y hy0
  rw [leafAt_leafWithCell _ _ _ (by omega) (by omega), ex, ey]
  rfl

theorem leafAt_leafWithCell_fun (leaf : UInt64) (u v : Int32) (a c : ℤ) (hu : u.toInt = a) (hv : v.toInt = c)
    (ha0 : 0 ≤ a) (ha : a < 8) (hc0 : 0 ≤ c) (hc : c < 8) (b : Bool) :
    leafAt (leafWithCell leaf u.toUInt32 v.toUInt32 b) = updatedAt (leafAt leaf) a c b := by
  funext x' y'
  subst hu hv
  exact leafAt_leafWithCell_int32 _ _ _ ha0 ha hc0 hc b x' y'

/--
The Kotlin `withCell` update of a MacroCell keeps it well-formed and hash-consistent, and sets exactly the cell
`(x, y)` to `b` (leaving the node unchanged when `(x, y)` is outside it).
-/
theorem macroCellWithCell_correct : ∀ (m : MacroCell) {d : ℕ}, WFd m d → d ≤ 30 → HashOK m →
    ∀ (x y : Int32) (b : Bool),
      WFd (macroCellWithCell m x y b) d ∧ HashOK (macroCellWithCell m x y b) ∧
      ∀ x' y', cellAt (macroCellWithCell m x y b) x' y' =
        if 0 ≤ x.toInt ∧ x.toInt < 2 ^ d ∧ 0 ≤ y.toInt ∧ y.toInt < 2 ^ d then
          updatedAt (cellAt m) x.toInt y.toInt b x' y'
        else cellAt m x' y' := by
  intro m
  induction m with
  | level4Node h nw ne sw se =>
    intro d hm hd H x y b
    rw [WFd_level4Node_iff] at hm
    subst hm
    rw [macroCellWithCell, show (MacroCell.level4Node h nw ne sw se).level = 4 from rfl,
      show (2 : ℤ) ^ 4 = 16 by decide, cellAt_level4Node_fun]
    have hw : ((1 : Int32) <<< (4 : UInt32).toInt32).toInt = 16 := by decide
    have hh : ((1 : Int32) <<< ((4 : UInt32).toInt32 - 1)).toInt = 8 := by decide
    generalize (1 : Int32) <<< (4 : UInt32).toInt32 = W at hw ⊢
    generalize (1 : Int32) <<< ((4 : UInt32).toInt32 - 1) = Hh at hh ⊢
    have hxl := x.toInt_lt; have hxg := x.le_toInt
    have hyl := y.toInt_lt; have hyg := y.le_toInt
    by_cases hin : 0 ≤ x.toInt ∧ x.toInt < 16 ∧ 0 ≤ y.toInt ∧ y.toInt < 16
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le,
          hw, Int32.toInt_zero]
        omega
      simp only [c, Bool.false_eq_true, ↓reduceIte, ite_pos' hin]
      by_cases hx8 : x.toInt < 8 <;> by_cases hy8 : y.toInt < 8
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true]
        refine ⟨rfl, rfl, fun x' y' => ?_⟩
        rw [cellAt_makeLevel4Node_fun, leafAt_leafWithCell_fun _ _ _ _ _ rfl rfl (by omega) hx8 (by omega) hy8]
        exact quadSel_update_nw _ _ _ _ _ _ _ _ ⟨by omega, hx8⟩ ⟨by omega, hy8⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true, decide_false]
        refine ⟨rfl, rfl, fun x' y' => ?_⟩
        rw [cellAt_makeLevel4Node_fun, leafAt_leafWithCell_fun _ _ _ _ (y.toInt - 8) rfl
          (by rw [int32_toInt_sub_of_range y Hh (by omega) (by omega), hh]) (by omega) hx8 (by omega) (by omega)]
        exact quadSel_update_sw _ _ _ _ _ _ _ _ ⟨by omega, hx8⟩ ⟨by omega, by omega⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_true, decide_false]
        refine ⟨rfl, rfl, fun x' y' => ?_⟩
        rw [cellAt_makeLevel4Node_fun, leafAt_leafWithCell_fun _ _ _ (x.toInt - 8) _
          (by rw [int32_toInt_sub_of_range x Hh (by omega) (by omega), hh]) rfl (by omega) (by omega) (by omega) hy8]
        exact quadSel_update_ne _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, hy8⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hx8, hy8, decide_false]
        refine ⟨rfl, rfl, fun x' y' => ?_⟩
        rw [cellAt_makeLevel4Node_fun, leafAt_leafWithCell_fun _ _ _ (x.toInt - 8) (y.toInt - 8)
          (by rw [int32_toInt_sub_of_range x Hh (by omega) (by omega), hh])
          (by rw [int32_toInt_sub_of_range y Hh (by omega) (by omega), hh]) (by omega) (by omega) (by omega) (by omega)]
        exact quadSel_update_se _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x' y'
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hw,
          Int32.toInt_zero]
        omega
      simp only [c, ↓reduceIte, ite_neg' hin]
      exact ⟨rfl, H, fun _ _ => rfl⟩
  | cellNode h nw ne sw se ih1 ih2 ih3 ih4 =>
    intro d hm hd H x y b
    obtain ⟨h5, h1, h2, h3, h4⟩ := hm
    obtain ⟨_, H1, H2, H3, H4⟩ := H
    have hlev := level_eq_of_WFd (m := .cellNode h nw ne sw se) ⟨h5, h1, h2, h3, h4⟩ (by omega)
    rw [macroCellWithCell, hlev, cellAt_cellNode_fun, WFd_level_toNat h1 (by omega)]
    have hw := int32_shl_one d (by omega)
    have hh := int32_shl_one_pred d (by omega) (by omega)
    generalize (1 : Int32) <<< d.toUInt32.toInt32 = W at hw ⊢
    generalize (1 : Int32) <<< (d.toUInt32.toInt32 - 1) = Hh at hh ⊢
    have hp : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := pow_two_pred d (by omega)
    have hp30 := pow_two_le_pow_two_30 (d - 1) (by omega)
    have hpos := pow_two_pos (d - 1)
    have h30 : (2 : ℤ) ^ 30 = 1073741824 := by decide
    have hxl := x.toInt_lt; have hxg := x.le_toInt
    have hyl := y.toInt_lt; have hyg := y.le_toInt
    have hd1 : d - 1 + 1 = d := by omega
    have wmk := fun {a b c e : MacroCell} (ha : WFd a (d - 1)) (hb : WFd b (d - 1)) (hc : WFd c (d - 1))
      (he : WFd e (d - 1)) => hd1 ▸ WFd_makeCellNode ha hb hc he
    have cmk := fun {a b c e : MacroCell} (ha : WFd a (d - 1)) =>
      (show cellAt (makeCellNode a b c e) = quadSel (cellAt a) (cellAt b) (cellAt c) (cellAt e) (2 ^ (d - 1)) by
        funext x' y'; rw [cellAt_makeCellNode, WFd_level_toNat ha (by omega)])
    by_cases hin : 0 ≤ x.toInt ∧ x.toInt < 2 ^ d ∧ 0 ≤ y.toInt ∧ y.toInt < 2 ^ d
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le,
          hw, Int32.toInt_zero]
        omega
      simp only [c, Bool.false_eq_true, ↓reduceIte, ite_pos' hin]
      by_cases hxh : x.toInt < 2 ^ (d - 1) <;> by_cases hyh : y.toInt < 2 ^ (d - 1)
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true]
        obtain ⟨r1, r2, r3⟩ := ih1 h1 (by omega) H1 x y b
        have e : cellAt (macroCellWithCell nw x y b) = updatedAt (cellAt nw) x.toInt y.toInt b := by
          funext x' y'; rw [r3, ite_pos' ⟨by omega, hxh, by omega, hyh⟩]
        refine ⟨wmk r1 h2 h3 h4, HashOK_makeCellNode r2 H2 H3 H4, fun x' y' => ?_⟩
        rw [cmk r1, e]
        exact quadSel_update_nw _ _ _ _ _ _ _ _ ⟨by omega, hxh⟩ ⟨by omega, hyh⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true, decide_false]
        have ey := int32_toInt_sub_of_range y Hh (by omega) (by omega)
        obtain ⟨r1, r2, r3⟩ := ih3 h3 (by omega) H3 x (y - Hh) b
        have e : cellAt (macroCellWithCell sw x (y - Hh) b) = updatedAt (cellAt sw) x.toInt (y.toInt - 2 ^ (d - 1)) b := by
          funext x' y'; rw [r3, ite_pos' ⟨by omega, hxh, by omega, by omega⟩, ey, hh]
        refine ⟨wmk h1 h2 r1 h4, HashOK_makeCellNode H1 H2 r2 H4, fun x' y' => ?_⟩
        rw [cmk h1, e]
        exact quadSel_update_sw _ _ _ _ _ _ _ _ ⟨by omega, hxh⟩ ⟨by omega, by omega⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_true, decide_false]
        have ex := int32_toInt_sub_of_range x Hh (by omega) (by omega)
        obtain ⟨r1, r2, r3⟩ := ih2 h2 (by omega) H2 (x - Hh) y b
        have e : cellAt (macroCellWithCell ne (x - Hh) y b) = updatedAt (cellAt ne) (x.toInt - 2 ^ (d - 1)) y.toInt b := by
          funext x' y'; rw [r3, ite_pos' ⟨by omega, by omega, by omega, hyh⟩, ex, hh]
        refine ⟨wmk h1 r1 h3 h4, HashOK_makeCellNode H1 r2 H3 H4, fun x' y' => ?_⟩
        rw [cmk h1, e]
        exact quadSel_update_ne _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, hyh⟩ x' y'
      · simp only [Int32.lt_iff_toInt_lt, hh, hxh, hyh, decide_false]
        have ex := int32_toInt_sub_of_range x Hh (by omega) (by omega)
        have ey := int32_toInt_sub_of_range y Hh (by omega) (by omega)
        obtain ⟨r1, r2, r3⟩ := ih4 h4 (by omega) H4 (x - Hh) (y - Hh) b
        have e : cellAt (macroCellWithCell se (x - Hh) (y - Hh) b) =
            updatedAt (cellAt se) (x.toInt - 2 ^ (d - 1)) (y.toInt - 2 ^ (d - 1)) b := by
          funext x' y'; rw [r3, ite_pos' ⟨by omega, by omega, by omega, by omega⟩, ex, ey, hh]
        refine ⟨wmk h1 h2 h3 r1, HashOK_makeCellNode H1 H2 H3 r2, fun x' y' => ?_⟩
        rw [cmk h1, e]
        exact quadSel_update_se _ _ _ _ _ _ _ _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x' y'
    · have c : (x < 0 || y < 0 || x ≥ W || y ≥ W) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, hw,
          Int32.toInt_zero]
        omega
      simp only [c, ↓reduceIte, ite_neg' hin]
      exact ⟨⟨h5, h1, h2, h3, h4⟩, ⟨by assumption, H1, H2, H3, H4⟩,
        fun _ _ => by rw [cellAt_cellNode, WFd_level_toNat h1 (by omega)]⟩


theorem UInt32.toNat_log2' (a : UInt32) : a.log2.toNat = a.toNat.log2 := rfl

/--
`minimumMacroCellLevel span` is the smallest level of at least 4 whose width `2 ^ level` covers `span` cells.
-/
theorem minimumMacroCellLevel_spec (span : UInt32) :
    4 ≤ (minimumMacroCellLevel span).toNat ∧ span.toNat ≤ 2 ^ (minimumMacroCellLevel span).toNat ∧
      ((minimumMacroCellLevel span).toNat = 4 ∨ 2 ^ ((minimumMacroCellLevel span).toNat - 1) < span.toNat) := by
  unfold minimumMacroCellLevel
  have hs := span.toNat_lt
  by_cases h16 : span ≤ 16
  · rw [UInt32.le_iff_toNat_le] at h16
    simp only [UInt32.le_iff_toNat_le, h16, ↓reduceIte]
    simp at h16 ⊢
    omega
  · have h16' : 17 ≤ span.toNat := by rw [UInt32.le_iff_toNat_le] at h16; simp at h16; omega
    have hsub : (span - 1).toNat = span.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; rfl
    have hne : span.toNat - 1 ≠ 0 := by omega
    have hlog : 4 ≤ (span.toNat - 1).log2 := (Nat.le_log2 hne).2 (by simp; omega)
    have hlog32 : (span.toNat - 1).log2 < 32 := (Nat.log2_lt hne).2 (by simp; omega)
    have hL : ((span - 1).log2 + 1).toNat = (span.toNat - 1).log2 + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_log2', hsub]; simp; omega
    have hc : ¬ ((span - 1).log2 + 1 < 4) := by rw [UInt32.lt_iff_toNat_lt, hL]; simp; omega
    simp only [h16, ↓reduceIte, hc, hL]
    refine ⟨by omega, ?_, Or.inr ?_⟩
    · have := Nat.lt_log2_self (n := span.toNat - 1)
      omega
    · rw [show (span.toNat - 1).log2 + 1 - 1 = (span.toNat - 1).log2 by omega]
      have := Nat.log2_self_le hne
      omega

/-- Kotlin's `emptySubnode` is the pre-built empty node of the argument's level (`EMPTY_NODES[level]`). -/
theorem emptySubnode_eq_emptyNode {m : MacroCell} {d : ℕ} (hm : WFd m d) : emptySubnode m = emptyNode d := by
  have h4 := WFd_ge_four hm
  have := emptySubnode_of_WFd (d := d - 4) (by rwa [show d - 4 + 4 = d by omega])
  rwa [show d - 4 + 4 = d by omega] at this

-- =========================================================================
-- Kotlin MacroCell members
-- =========================================================================

/-- `Level4Node.cellEquals` (Kotlin's `Level4Node.equals`) is equality of Level 4 nodes. -/
theorem level4Node_cellEquals_iff (h1 h2 : UInt32) (a1 b1 c1 d1 a2 b2 c2 d2 : UInt64) :
    Level4Node.cellEquals (.level4Node h1 a1 b1 c1 d1) (.level4Node h2 a2 b2 c2 d2) = true ↔
      MacroCell.level4Node h1 a1 b1 c1 d1 = .level4Node h2 a2 b2 c2 d2 := by
  simp [Level4Node.cellEquals, and_assoc]

/-- `CellNode.cellEquals` (Kotlin's `CellNode.equals`) is equality of CellNodes. -/
theorem cellNode_cellEquals_iff (h1 h2 : UInt32) (a1 b1 c1 d1 a2 b2 c2 d2 : MacroCell) :
    CellNode.cellEquals (.cellNode h1 a1 b1 c1 d1) (.cellNode h2 a2 b2 c2 d2) = true ↔
      MacroCell.cellNode h1 a1 b1 c1 d1 = .cellNode h2 a2 b2 c2 d2 := by
  simp only [CellNode.cellEquals, Bool.and_eq_true, beq_iff_eq, macroCell_cellEquals_iff_eq_Impl,
    MacroCell.cellNode.injEq, and_assoc]

/--
The `UInt64` population `MacroCell.size` (Kotlin's cached `size()`) is the exact number of live cells of a
well-formed node of depth at most 31.
-/
theorem size_toNat_of_WFd {m : MacroCell} {d : ℕ} (hm : WFd m d) (hd : d ≤ 31) : m.size.toNat = macroCellSize m := by
  rw [size_toNat]
  have h1 := macroCellSize_le_pow hm
  have h2 : 4 ^ d ≤ 4 ^ 31 := Nat.pow_le_pow_right (by decide) hd
  have h3 : (4 : ℕ) ^ 31 < 2 ^ 64 := by decide
  exact Nat.mod_eq_of_lt (by omega)

end Algorithm

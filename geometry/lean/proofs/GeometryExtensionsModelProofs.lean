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

import Mathlib.Tactic
import models.GeometryExtensionsModel

namespace Geometry.KotlinModel

/-- Injectivity of `Int32.toUInt32`. -/
theorem int32_toUInt32_inj {a b : Int32} (h : a.toUInt32 = b.toUInt32) : a = b := by
  cases a; cases b; cases h; rfl

/-- Injectivity of `UInt32.toInt32`. -/
theorem uint32_toInt32_inj {a b : UInt32} (h : a.toInt32 = b.toInt32) : a = b := by
  cases a; cases b
  injection h with h'

/-- Unpacking `x` from `packOffset x y` recovers `x`. -/
theorem offsetX_pack (x y : Int32) : offsetX (packOffset x y) = x := by
  rcases x with ⟨⟨bx⟩⟩
  rcases y with ⟨⟨by_⟩⟩
  apply int32_toUInt32_inj
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((((BitVec.setWidth 64 bx) <<< 32) ||| (BitVec.setWidth 64 by_)) >>> 32).setWidth 32).getLsbD i =
    bx.getLsbD i
  have hi64 : i < 64 := by omega
  have h1 : 32 + i < 64 := by omega
  have h2 : ¬ (32 + i < 32) := by omega
  have h3 : 32 + i - 32 = i := by omega
  simp [hi, hi64, h1, h2, h3]

/-- Unpacking `y` from `packOffset x y` recovers `y`. -/
theorem offsetY_pack (x y : Int32) : offsetY (packOffset x y) = y := by
  rcases x with ⟨⟨bx⟩⟩
  rcases y with ⟨⟨by_⟩⟩
  apply int32_toUInt32_inj
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((((BitVec.setWidth 64 bx) <<< 32) ||| (BitVec.setWidth 64 by_)).setWidth 32)).getLsbD i =
    by_.getLsbD i
  simp [hi]

/-- Re-packing `(offsetX p, offsetY p)` recovers `p`. -/
theorem packOffset_unpack (p : UInt64) : packOffset (offsetX p) (offsetY p) = p := by
  rcases p with ⟨bp⟩
  apply congrArg UInt64.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((BitVec.setWidth 64 ((bp >>> 32).setWidth 32)) <<< 32) |||
    (BitVec.setWidth 64 (bp.setWidth 32))).getLsbD i = bp.getLsbD i
  by_cases hlt : i < 32
  · simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, hlt]
  · have hi_sub : i - 32 < 32 := by omega
    have hi_sub64 : i - 32 < 64 := by omega
    have hadd : 32 + (i - 32) = i := by omega
    simp [BitVec.getLsbD_setWidth, hi, hlt, hi_sub, hi_sub64, hadd]

/-- Helper connecting `v.toInt32.toInt` directly to `v.toNat`. -/
theorem uint32_toInt32_toInt (v : UInt32) :
    v.toInt32.toInt = if 2 * v.toNat < 2 ^ 32 then (v.toNat : Int) else (v.toNat : Int) - 2 ^ 32 := by
  change v.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_cond]
  rfl

/-- Signed `Int` value of `absI32UInt v` equals `Int.natAbs v.toInt32.toInt` when `v ≠ 0x80000000`. -/
theorem absI32UInt_toInt {v : UInt32} (hne : v ≠ 0x80000000) :
    (absI32UInt v).toInt32.toInt = (v.toInt32.toInt).natAbs := by
  dsimp [absI32UInt]
  have hv_lt : v.toNat < 2 ^ 32 := v.toNat_lt
  have hv_ne : v.toNat ≠ 2 ^ 31 := fun h => hne (UInt32.toNat.inj h)
  have hslt : v.toBitVec.slt 0#32 = decide (v.toInt32.toInt < 0) := rfl
  have hvi := uint32_toInt32_toInt v
  rw [hslt]
  by_cases hneg : v.toInt32.toInt < 0
  · have hv_gt : 2 ^ 31 < v.toNat := by split at hvi <;> omega
    have hnv_nat : (-v).toNat = 2 ^ 32 - v.toNat := by
      change (2 ^ 32 - v.toNat) % 2 ^ 32 = 2 ^ 32 - v.toNat
      exact Nat.mod_eq_of_lt (by omega)
    have hnvi := uint32_toInt32_toInt (-v)
    rw [hnv_nat] at hnvi
    simp only [decide_eq_true hneg, ↓reduceIte]
    split at hvi <;> split at hnvi <;> omega
  · simp only [decide_eq_false hneg, Bool.false_eq_true, ↓reduceIte]
    split at hvi <;> omega

theorem absI32UInt_nonneg_toNat {v : UInt32} (hne : v ≠ 0x80000000) :
    (absI32UInt v).toBitVec.slt 0#32 = false ∧ (absI32UInt v).toNat = (v.toInt32.toInt).natAbs := by
  have hi := absI32UInt_toInt hne
  have hslt : (absI32UInt v).toBitVec.slt 0#32 = decide ((absI32UInt v).toInt32.toInt < 0) := rfl
  have hslt_f : (absI32UInt v).toBitVec.slt 0#32 = false := by
    rw [hslt, decide_eq_false (by omega)]
  have hai := uint32_toInt32_toInt (absI32UInt v)
  rw [hi] at hai
  have halt : (absI32UInt v).toNat < 2 ^ 32 := (absI32UInt v).toNat_lt
  refine ⟨hslt_f, ?_⟩
  split at hai <;> omega

private theorem uint32_neg_neg (u : UInt32) : -(-u) = u := by
  rcases u with ⟨b⟩
  apply congrArg UInt32.ofBitVec
  exact BitVec.neg_neg

theorem absI32UInt_neg (x : Int32) :
    absI32UInt (-x).toUInt32 = absI32UInt x.toUInt32 := by
  dsimp [absI32UInt]
  have hneg_u32 : (-x).toUInt32 = -x.toUInt32 := rfl
  rw [hneg_u32]
  have hx_lt : x.toUInt32.toNat < 2 ^ 32 := x.toUInt32.toNat_lt
  have hslt1 : x.toUInt32.toBitVec.slt 0#32 = decide (x.toUInt32.toInt32.toInt < 0) := rfl
  have hslt2 : (-x.toUInt32).toBitVec.slt 0#32 = decide ((-x.toUInt32).toInt32.toInt < 0) := rfl
  have hxi := uint32_toInt32_toInt x.toUInt32
  have hnvi := uint32_toInt32_toInt (-x.toUInt32)
  have hnv_nat : (-x.toUInt32).toNat = if x.toUInt32.toNat = 0 then 0 else 2 ^ 32 - x.toUInt32.toNat := by
    change (2 ^ 32 - x.toUInt32.toNat) % 2 ^ 32 = _
    split
    · next h0 => simp [h0]
    · next hne => exact Nat.mod_eq_of_lt (by omega)
  by_cases h0 : x.toUInt32.toNat = 0
  · have hx0 : x.toUInt32 = 0 := UInt32.toNat.inj h0
    simp [hx0]
  by_cases hmin : x.toUInt32.toNat = 2 ^ 31
  · have hxmin : x.toUInt32 = 0x80000000 := UInt32.toNat.inj hmin
    rw [hxmin]
    decide
  have hnn : -(-x.toUInt32) = x.toUInt32 := uint32_neg_neg x.toUInt32
  simp only [hnv_nat, h0, ↓reduceIte] at hnvi
  rw [hslt1, hslt2]
  split at hxi <;> split at hnvi
  · exfalso; omega
  · rw [decide_eq_true (by omega : (-x.toUInt32).toInt32.toInt < 0),
      decide_eq_false (by omega : ¬ x.toUInt32.toInt32.toInt < 0)]
    simp [hnn]
  · rw [decide_eq_false (by omega : ¬ (-x.toUInt32).toInt32.toInt < 0),
      decide_eq_true (by omega : x.toUInt32.toInt32.toInt < 0)]
    simp
  · exfalso; omega

/-- Cancellation `(a + b) - b = a` on `Int32` even with wrap-around. -/
theorem int32_add_sub_cancel_right (a b : Int32) : a + b - b = a := by
  rcases a with ⟨⟨ba⟩⟩; rcases b with ⟨⟨bb⟩⟩
  apply int32_toUInt32_inj
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_toNat_eq
  change (2 ^ 32 - bb.toNat + (ba.toNat + bb.toNat) % 2 ^ 32) % 2 ^ 32 = ba.toNat
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have ha : ba.toNat < 2 ^ 32 := ba.isLt
  have hb : bb.toNat < 2 ^ 32 := bb.isLt
  have hsum : 2 ^ 32 - bb.toNat + (ba.toNat + bb.toNat) = 2 ^ 32 + ba.toNat := by omega
  rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

/-- Right cancellation `a + c = b + c → a = b` on `Int32`. -/
theorem int32_add_right_cancel {a b c : Int32} (h : a + c = b + c) : a = b := by
  have h1 := congrArg (· - c) h
  simpa only [int32_add_sub_cancel_right] using h1

/-- Non-overflowing signed `Int32` addition preserves exact integer sum. -/
theorem int32_toInt_add_of_bounds {a b : Int32}
    (hlo : -(2 ^ 31 : Int) ≤ a.toInt + b.toInt) (hhi : a.toInt + b.toInt < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]
  unfold Int.bmod
  dsimp only
  split <;> omega

end Geometry.KotlinModel

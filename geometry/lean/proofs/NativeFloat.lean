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

import models.FloatModel
import GeometryDefs
import proofs.FloatAnalysis
import proofs.RayMarchLimits
import FloatLib
import Mathlib.Tactic

/-!
# Lean's native `Float` agrees with FloatLib's binary64 model

The compiled ray march (`Geometry/LineSegment.lean`) computes with Lean's native `Float`, while the
float model (`models/FloatModel.lean`) computes with FloatLib's `Binary64`. In Lean 4.34, `Float`
arithmetic and comparisons have a logical model (`Float.Model`, an IEEE-754 binary64 word unpacked to
`Float.Model.UnpackedFloat`). This file proves that the operations the ray march uses agree with
FloatLib's: comparisons and multiplication (FloatLib already proves subtraction), negation,
`Int32.toFloat` and the literal `0.0`.

The results are stated through `Agree`: a native float and a FloatLib value agree when both are
finite and denote the same real number. Agreement is preserved by every operation of the ray march,
and agreeing operands give the same comparison results.
-/

namespace Geometry

open Float.Model
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model

/-! ## Canonical unpacked binary64 values -/

/-- The finite values produced by unpacking a binary64 word: normal or on the subnormal grid. -/
def Canon (u : UnpackedFloat) : Prop :=
  ∀ s m e h, u = .finite s m e h →
    m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (2 ^ 52 ≤ m ∨ e = -1074)

theorem unpack_binary64_finite {b : BitVec 64} {s : UnpackedFloat.Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hu : UnpackedFloat.unpack Format.binary64 b = .finite s m e h) :
    m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (2 ^ 52 ≤ m ∨ e = -1074) := by
  unfold UnpackedFloat.unpack at hu
  simp only at hu
  have h1 : (UnpackedFloat.unpackMantissa (spec := Format.binary64) b).toNat < 2 ^ 52 :=
    BitVec.isLt _
  by_cases hE1 : UnpackedFloat.unpackExponent (spec := Format.binary64) b = -1#_
  · simp only [hE1, ↓reduceIte] at hu
    split at hu <;> cases hu
  · simp only [hE1, ↓reduceIte] at hu
    by_cases hE0 : UnpackedFloat.unpackExponent (spec := Format.binary64) b = 0#_
    · simp only [hE0, ↓reduceIte] at hu
      by_cases hM : UnpackedFloat.unpackMantissa (spec := Format.binary64) b = 0#_
      · simp only [hM, ↓reduceDIte] at hu
        cases hu
      · simp only [hM, ↓reduceDIte] at hu
        injection hu with _ hm he
        subst hm he
        refine ⟨by omega, ?_, ?_, Or.inr ?_⟩ <;> simp [Format.exponentBias]
    · simp only [hE0, ↓reduceIte] at hu
      injection hu with _ hm he
      subst hm he
      have h3 : (UnpackedFloat.unpackExponent (spec := Format.binary64) b).toNat ≠ 0 := by
        intro h0; apply hE0; exact BitVec.eq_of_toNat_eq (by simpa using h0)
      have happ : (1#1 ++ UnpackedFloat.unpackMantissa (spec := Format.binary64) b).toNat =
          2 ^ 52 + (UnpackedFloat.unpackMantissa (spec := Format.binary64) b).toNat := by
        rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt h1]
        simp [Nat.shiftLeft_eq]
      have h4 : (UnpackedFloat.unpackExponent (spec := Format.binary64) b).toNat < 2047 := by
        have hlt : (UnpackedFloat.unpackExponent (spec := Format.binary64) b).toNat < 2 ^ 11 :=
          BitVec.isLt _
        have hne : (UnpackedFloat.unpackExponent (spec := Format.binary64) b).toNat ≠ 2047 := by
          intro h7; apply hE1; exact BitVec.eq_of_toNat_eq (by simpa using h7)
        omega
      rw [happ]
      refine ⟨by omega, ?_, ?_, Or.inl (by omega)⟩ <;> simp [Format.exponentBias] <;> omega

theorem canon_unpack (x : Float) : Canon x.toModel.unpack :=
  fun _ _ _ _ hu => unpack_binary64_finite hu
/-! ## Comparisons -/

local notation "bp" => FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix

theorem bp_pos (e : ℤ) : 0 < bp e := by
  unfold FloatLib.Floats.Formats.Flocq.bpow
  simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  positivity

theorem bp_add (a b : ℤ) : bp (a + b) = bp a * bp b := by
  unfold FloatLib.Floats.Formats.Flocq.bpow
  rw [zpow_add₀]
  simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

/-- Canonical magnitudes are ordered by exponent first. -/
theorem mag_lt_of_exp_lt {m1 m2 : ℕ} {e1 e2 : ℤ}
    (c1 : m1 < 2 ^ 53) (c2 : 2 ^ 52 ≤ m2 ∨ e2 = -1074) (he1 : -1074 ≤ e1) (h : e1 < e2) :
    (m1 : ℝ) * bp e1 < (m2 : ℝ) * bp e2 := by
  have hm2 : 2 ^ 52 ≤ m2 := by
    rcases c2 with h2 | h2
    · exact h2
    · omega
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, e2 = e1 + 1 + k := ⟨(e2 - e1 - 1).toNat, by omega⟩
  have hb : bp (e1 + 1 + k) = bp e1 * 2 * 2 ^ k := by
    rw [bp_add, bp_add]
    unfold FloatLib.Floats.Formats.Flocq.bpow
    simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
  rw [hb]
  have hpos := bp_pos e1
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h1 : (m1 : ℝ) < 2 ^ 53 := by exact_mod_cast c1
  have h2 : (2 : ℝ) ^ 52 ≤ m2 := by exact_mod_cast hm2
  have : (m1 : ℝ) * bp e1 < 2 ^ 53 * bp e1 := by nlinarith
  calc (m1 : ℝ) * bp e1 < 2 ^ 53 * bp e1 := this
    _ = 2 ^ 52 * (bp e1 * 2 * 1) := by ring
    _ ≤ (m2 : ℝ) * (bp e1 * 2 * 2 ^ k) := by
      apply mul_le_mul h2 _ (by positivity) (by positivity)
      nlinarith

theorem compare_pos_finite {m1 m2 : ℕ} {e1 e2 : ℤ}
    (c1 : m1 < 2 ^ 53 ∧ -1074 ≤ e1 ∧ (2 ^ 52 ≤ m1 ∨ e1 = -1074))
    (c2 : m2 < 2 ^ 53 ∧ -1074 ≤ e2 ∧ (2 ^ 52 ≤ m2 ∨ e2 = -1074)) :
    (compare e1 e2).then (compare m1 m2) = compare ((m1 : ℝ) * bp e1) ((m2 : ℝ) * bp e2) := by
  rcases lt_trichotomy e1 e2 with h | h | h
  · rw [(compare_lt_iff_lt).mpr h, Ordering.lt_then]
    exact ((compare_lt_iff_lt).mpr (mag_lt_of_exp_lt c1.1 c2.2.2 c1.2.1 h)).symm
  · subst h
    rw [(compare_eq_iff_eq).mpr rfl, Ordering.eq_then]
    have hpos := bp_pos e1
    rcases lt_trichotomy m1 m2 with hm | hm | hm
    · rw [(compare_lt_iff_lt).mpr hm, (compare_lt_iff_lt).mpr]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hm) hpos
    · subst hm; rw [(compare_eq_iff_eq).mpr rfl, (compare_eq_iff_eq).mpr rfl]
    · rw [(compare_gt_iff_gt).mpr hm, (compare_gt_iff_gt).mpr]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hm) hpos
  · rw [(compare_gt_iff_gt).mpr h, Ordering.gt_then]
    exact ((compare_gt_iff_gt).mpr (mag_lt_of_exp_lt c2.1 c1.2.2 c2.2.1 h)).symm

theorem compare_neg_neg (a b : ℝ) : compare (-a) (-b) = (compare a b).swap := by
  rcases lt_trichotomy a b with h | h | h
  · rw [(compare_lt_iff_lt).mpr h, (compare_gt_iff_gt).mpr (neg_lt_neg h)]; rfl
  · subst h; rw [(compare_eq_iff_eq).mpr rfl, (compare_eq_iff_eq).mpr rfl]; rfl
  · rw [(compare_gt_iff_gt).mpr h, (compare_lt_iff_lt).mpr (neg_lt_neg h)]; rfl

theorem canon_of_finite {u : UnpackedFloat} (cu : Canon u) {s m e h} (hu : u = .finite s m e h) :
    m < 2 ^ 53 ∧ -1074 ≤ e ∧ (2 ^ 52 ≤ m ∨ e = -1074) :=
  ⟨(cu s m e h hu).1, (cu s m e h hu).2.1, (cu s m e h hu).2.2.2⟩

/-- On canonical finite values, Lean's unpacked comparison is the comparison of real values. -/
theorem unpacked_compare_eq (u v : UnpackedFloat) (hu : u.isFinite = true) (hv : v.isFinite = true)
    (cu : Canon u) (cv : Canon v) :
    u.compare v = some (compare (unpackedToReal u) (unpackedToReal v)) := by
  have hm_pos : ∀ (m : ℕ) (e : ℤ), 0 < m → 0 < (m : ℝ) * bp e := fun m e hm =>
    mul_pos (by exact_mod_cast hm) (bp_pos e)
  cases u with
  | notANumber => simp [UnpackedFloat.isFinite] at hu
  | infinity _ => simp [UnpackedFloat.isFinite] at hu
  | zero s1 =>
    cases v with
    | notANumber => simp [UnpackedFloat.isFinite] at hv
    | infinity _ => simp [UnpackedFloat.isFinite] at hv
    | zero s2 =>
      simp only [unpackedToReal_zero, (compare_eq_iff_eq).mpr rfl]
      rfl
    | finite s2 m2 e2 h2 =>
      have := hm_pos m2 e2 h2
      cases s2 <;> simp only [unpackedToReal_zero, unpackedToReal_finite, modelSignBit] <;>
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
      · rw [(compare_gt_iff_gt).mpr (by linarith)]; rfl
      · rw [(compare_lt_iff_lt).mpr (by linarith)]; rfl
  | finite s1 m1 e1 h1 =>
    have c1 := canon_of_finite cu rfl
    have p1 := hm_pos m1 e1 h1
    cases v with
    | notANumber => simp [UnpackedFloat.isFinite] at hv
    | infinity _ => simp [UnpackedFloat.isFinite] at hv
    | zero s2 =>
      cases s1 <;> simp only [unpackedToReal_zero, unpackedToReal_finite, modelSignBit] <;>
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
      · rw [(compare_lt_iff_lt).mpr (by linarith)]; rfl
      · rw [(compare_gt_iff_gt).mpr (by linarith)]; rfl
    | finite s2 m2 e2 h2 =>
      have c2 := canon_of_finite cv rfl
      have p2 := hm_pos m2 e2 h2
      cases s1 <;> cases s2 <;> simp only [unpackedToReal_finite, modelSignBit] <;>
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
      · rw [neg_mul, neg_mul, compare_neg_neg, ← compare_pos_finite c1 c2]; rfl
      · rw [(compare_lt_iff_lt).mpr (by linarith)]; rfl
      · rw [(compare_gt_iff_gt).mpr (by linarith)]; rfl
      · rw [← compare_pos_finite c1 c2]; rfl

theorem ofFloat_isFinite (x : Float) :
    ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat x) = x.isFinite := by
  change Model.isFinite (Model.ofFloatModel x.toModel) = x.toModel.unpack.isFinite
  rw [← toDyadic?_isSome_eq_isFinite, toDyadic?_ieee_eq_model _ (by decide), toModel_ofFloatModel]
  cases x.toModel.unpack <;> rfl

theorem toReal_ofFloat (x : Float) :
    Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat x)) = unpackedToReal x.toModel.unpack := by
  change Model.toReal (Model.ofFloatModel x.toModel) = _
  rw [toReal_eq_unpackedToReal_toModel (by decide), toModel_ofFloatModel]

theorem native_compare (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x.toModel.unpack.compare y.toModel.unpack =
      some (compare (unpackedToReal x.toModel.unpack) (unpackedToReal y.toModel.unpack)) :=
  unpacked_compare_eq _ _ hx hy (canon_unpack x) (canon_unpack y)

theorem native_lt_unfold (x y : Float) :
    x < y ↔ (x.toModel.unpack.compare y.toModel.unpack == some .lt) = true := by
  show Float.lt x y = true ↔ _
  unfold Float.lt
  simp only [decide_eq_true_eq]
  rfl

theorem native_le_unfold (x y : Float) :
    x ≤ y ↔ (x.toModel.unpack.compare y.toModel.unpack).any (·.isLE) = true := by
  show Float.le x y = true ↔ _
  unfold Float.le
  simp only [decide_eq_true_eq]
  rfl

theorem native_lt_iff (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x < y ↔ ExecFloat.Binary.ofFloat x < ExecFloat.Binary.ofFloat y := by
  have hfx : ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat x) = true := by rw [ofFloat_isFinite]; exact hx
  have hfy : ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat y) = true := by rw [ofFloat_isFinite]; exact hy
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt,
    compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ hfx hfy, toReal_ofFloat, toReal_ofFloat]
  rw [native_lt_unfold, native_compare x y hx hy]
  simp [compare_lt_iff_lt]

theorem native_le_iff (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x ≤ y ↔ ExecFloat.Binary.ofFloat x ≤ ExecFloat.Binary.ofFloat y := by
  have hfx : ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat x) = true := by rw [ofFloat_isFinite]; exact hx
  have hfy : ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat y) = true := by rw [ofFloat_isFinite]; exact hy
  rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq,
    compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ hfx hfy,
    compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ hfx hfy, toReal_ofFloat, toReal_ofFloat]
  rw [native_le_unfold, native_compare x y hx hy]
  rcases lt_trichotomy (unpackedToReal x.toModel.unpack) (unpackedToReal y.toModel.unpack) with h | h | h
  · simp [(compare_lt_iff_lt).mpr h, h]
  · simp [h]
  · simp [(compare_gt_iff_gt).mpr h, h.ne', not_lt.mpr h.le]

/-! ## Multiplication -/

theorem round_eq_roundWithAccuracy (spec : Format) (s : UnpackedFloat.Sign) (M : ℕ) (E : ℤ)
    (h : E ≤ spec.targetExponent (totalExponent M E)) :
    UnpackedFloat.round spec s M E = UnpackedFloat.roundWithAccuracy spec s M E .exact := by
  unfold UnpackedFloat.round UnpackedFloat.decreaseExponent
  have : (E - spec.targetExponent (totalExponent M E)).toNat = 0 := by omega
  simp [this]

theorem mul_exponent_le (m1 m2 : ℕ) (e1 e2 : ℤ) (hm1 : 0 < m1) (hm2 : 0 < m2)
    (c1 : 2 ^ 52 ≤ m1 ∨ e1 = -1074) (c2 : 2 ^ 52 ≤ m2 ∨ e2 = -1074) :
    e1 + e2 ≤ Format.binary64.targetExponent (totalExponent (m1 * m2) (e1 + e2)) := by
  unfold Format.targetExponent totalExponent
  have hmin : Format.binary64.minExponent = -1074 := by decide
  have hbits : Format.binary64.mantissaBits = 53 := by decide
  rw [hmin, hbits]
  by_cases hbig : 2 ^ 52 ≤ m1 * m2
  · have : 52 ≤ (m1 * m2).log2 := (Nat.le_log2 (by positivity)).mpr hbig
    omega
  · have hs1 : e1 = -1074 := by
      rcases c1 with h | h
      · exact absurd (le_trans h (Nat.le_mul_of_pos_right m1 hm2)) hbig
      · exact h
    have hs2 : e2 = -1074 := by
      rcases c2 with h | h
      · exact absurd (le_trans h (Nat.le_mul_of_pos_left m2 hm1)) hbig
      · exact h
    omega

theorem modelSign_xor (s1 s2 : UnpackedFloat.Sign) :
    modelSign (Bool.xor (modelSignBit s1) (modelSignBit s2)) = s1 * s2 := by
  cases s1 <;> cases s2 <;> rfl

theorem mul_eq_ofModel_mul_binary64 (x y : Model FloatFormat.binary64)
    (hx : (toModel x).isFinite = true) (hy : (toModel y).isFinite = true)
    (cx : Canon (toModel x)) (cy : Canon (toModel y)) :
    Model.mul x y = ofModel FloatFormat.binary64
      (UnpackedFloat.mul (FloatFormat.toModel FloatFormat.binary64) (toModel x) (toModel y)) := by
  have hfmt : FloatFormat.binary64.isIEEE = true := by decide
  cases hxm : toModel x <;> cases hym : toModel y <;>
    simp only [hxm, hym, UnpackedFloat.isFinite, Bool.false_eq_true] at hx hy
  case zero.zero s1 s2 =>
    rw [Proof.mul_eq_spec, Spec.mul, toDyadic?_ieee_eq_model _ hfmt x, toDyadic?_ieee_eq_model _ hfmt y,
      hxm, hym]
    cases s1 <;> cases s2 <;> simp [unpackedToDyadic?, UnpackedFloat.mul, modelSignBit] <;> rfl
  case zero.finite s1 s2 m2 e2 h2 =>
    rw [Proof.mul_eq_spec, Spec.mul, toDyadic?_ieee_eq_model _ hfmt x, toDyadic?_ieee_eq_model _ hfmt y,
      hxm, hym]
    cases s1 <;> cases s2 <;> simp [unpackedToDyadic?, UnpackedFloat.mul, modelSignBit] <;> rfl
  case finite.zero s1 m1 e1 h1 s2 =>
    rw [Proof.mul_eq_spec, Spec.mul, toDyadic?_ieee_eq_model _ hfmt x, toDyadic?_ieee_eq_model _ hfmt y,
      hxm, hym]
    cases s1 <;> cases s2 <;> simp [unpackedToDyadic?, UnpackedFloat.mul, modelSignBit] <;> rfl
  case finite.finite s1 m1 e1 h1 s2 m2 e2 h2 =>
    have c1 := canon_of_finite cx hxm
    have c2 := canon_of_finite cy hym
    rw [Proof.mul_eq_spec, Spec.mul, toDyadic?_ieee_eq_model _ hfmt x, toDyadic?_ieee_eq_model _ hfmt y,
      hxm, hym]
    simp only [unpackedToDyadic?]
    have hne : (m1 == 0 || m2 == 0) = false := by
      simp [Nat.pos_iff_ne_zero.mp h1, Nat.pos_iff_ne_zero.mp h2]
    simp only [hne, Bool.false_eq_true, ↓reduceIte, roundDyadic, hfmt, ieeeRoundDyadic]
    rw [modelSign_xor, round_eq_roundWithAccuracy (FloatFormat.toModel FloatFormat.binary64) _ _ _
      (mul_exponent_le m1 m2 e1 e2 h1 h2 c1.2.2 c2.2.2)]
    rfl

theorem toModel_ofFloat_mul (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat (x * y)) =
      Model.mul (ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat x))
        (ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat y)) := by
  rw [ExecFloat.Binary.toModel_ofFloat, ExecFloat.Binary.toModel_ofFloat, ExecFloat.Binary.toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.mul x.toModel y.toModel) = _
  rw [Float.Model.mul, Model.ofFloatModel_pack]
  have h := mul_eq_ofModel_mul_binary64 (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using hx)
    (by simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using hy)
    (by rw [Model.toModel_ofFloatModel]; exact canon_unpack x)
    (by rw [Model.toModel_ofFloatModel]; exact canon_unpack y)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/-- Native binary64 multiplication equals FloatLib's binary64 multiplication on finite inputs. -/
theorem ofFloat_mul_of_isFinite (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ExecFloat.Binary.ofFloat (x * y) = ExecFloat.Binary.ofFloat x * ExecFloat.Binary.ofFloat y := by
  apply Configured.Family.toModel_injective
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat (x * y)) =
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat x * ExecFloat.Binary.ofFloat y)
  rw [toModel_mul_binary64, ← Model.Proof.mul_eq_spec]
  exact toModel_ofFloat_mul x y hx hy

/-! ## Negation, integer conversion and zero -/

/-- Packing a canonical unpacked binary64 value and unpacking it again is the identity. -/
theorem unpack_pack_canon (u : UnpackedFloat) (hu : u.isFinite = true) (cu : Canon u) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u) = u := by
  cases u with
  | notANumber => simp [UnpackedFloat.isFinite] at hu
  | infinity _ => simp [UnpackedFloat.isFinite] at hu
  | zero s => exact unpack_pack_zero _ s
  | finite s m e h =>
    obtain ⟨hm53, he0, he1, hnorm⟩ := cu s m e h rfl
    by_cases hbig : 2 ^ 52 ≤ m
    · have hlog : m.log2 + 1 = Format.binary64.mantissaBits := by
        have h1 : 52 ≤ m.log2 := (Nat.le_log2 (by omega)).mpr hbig
        have h2 : m.log2 < 53 := (Nat.log2_lt (by omega)).mpr hm53
        have : Format.binary64.mantissaBits = 53 := by decide
        omega
      have := unpack_pack_finite_normal Format.binary64 s m e (by omega) hlog
        (by simp [Format.exponentBias]; omega) (by simp [Format.exponentBias]; omega)
        (by simp [Format.exponentBias]; omega)
      exact this
    · have he : e = FloatFormat.ieeeMinSubnormalExponent FloatFormat.binary64 := by
        rcases hnorm with h' | h'
        · omega
        · rw [h']; decide
      subst he
      exact unpack_pack_finite_subnormal FloatFormat.binary64 s m (by omega)
        (by change m < 2 ^ 52; omega)

theorem canon_neg {u : UnpackedFloat} (cu : Canon u) : Canon u.neg := by
  intro s m e h hu
  cases u with
  | notANumber => cases hu
  | infinity _ => cases hu
  | zero _ => cases hu
  | finite s' m' e' h' =>
    simp only [UnpackedFloat.neg, UnpackedFloat.finite.injEq] at hu
    obtain ⟨_, hm, he⟩ := hu
    subst hm he
    exact cu s' _ _ h' rfl

theorem unpackedToReal_neg (u : UnpackedFloat) : unpackedToReal u.neg = -unpackedToReal u := by
  cases u with
  | notANumber => simp [UnpackedFloat.neg, unpackedToReal, unpackedToDyadic?]
  | infinity _ => simp [UnpackedFloat.neg, unpackedToReal, unpackedToDyadic?]
  | zero s => simp [UnpackedFloat.neg]
  | finite s m e h =>
    cases s <;> simp [UnpackedFloat.neg, modelSignBit]

/-- Native negation of a finite float is finite and negates its real value. -/
theorem native_neg (x : Float) (hx : x.isFinite = true) :
    (-x).isFinite = true ∧ unpackedToReal (-x).toModel.unpack = -unpackedToReal x.toModel.unpack := by
  have hu : (-x).toModel.unpack = x.toModel.unpack.neg := by
    change UnpackedFloat.unpack Format.binary64
        (UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 x.toModel.unpack.neg)).toBitVec = _
    rw [UInt64.toBitVec_ofBitVec]
    apply unpack_pack_canon _ _ (canon_neg (canon_unpack x))
    have hfin : x.toModel.unpack.isFinite = true := hx
    cases h : x.toModel.unpack <;> simp_all [UnpackedFloat.isFinite, UnpackedFloat.neg]
  refine ⟨?_, by rw [hu, unpackedToReal_neg]⟩
  change (-x).toModel.unpack.isFinite = true
  have hfin : x.toModel.unpack.isFinite = true := hx
  rw [hu]
  cases h : x.toModel.unpack <;> simp_all [UnpackedFloat.isFinite, UnpackedFloat.neg]

/-- `Int32.toFloat` is FloatLib's integer conversion `intToBinary64`. -/
theorem ofFloat_int32ToFloat (n : Int32) :
    ExecFloat.Binary.ofFloat n.toFloat = intToBinary64 n.toInt := by
  apply Configured.Family.toModel_injective
  change ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat n.toFloat) =
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat (Float.ofInt n.toInt))
  rw [ExecFloat.Binary.toModel_ofFloat_ofInt, ExecFloat.Binary.toModel_ofFloat]
  simp only [Int32.toFloat, Float.Model.ofInt32, Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt32]
  exact Model.ofModel_ofInt_eq_roundDyadic _ (by decide) _

theorem native_zero_unpack : (0.0 : Float).toModel.unpack = .zero .positive := by
  rfl

/-! ## Agreement between native floats and FloatLib binary64 values -/

/-- The real value of a native float, read through FloatLib's binary64 model. -/
noncomputable def nreal (x : Float) : ℝ :=
  Model.toReal (ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat x))

/-- The real value of a FloatLib binary64 value. -/
noncomputable def breal (b : Binary64) : ℝ :=
  Model.toReal (ExecFloat.Binary.toModel b)

theorem nreal_eq (x : Float) : nreal x = unpackedToReal x.toModel.unpack :=
  toReal_ofFloat x

theorem toModel_sub_binary64 (x y : Binary64) :
    ExecFloat.Binary.toModel (x - y) =
      Model.Spec.sub (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) := by
  change ExecFloat.Binary.toModel (ExecFloat.sub x y) = _
  rw [ExecFloat.Proof.sub_eq_spec]
  change Configured.Family.toModel (ExecFloat.ModelCodec.liftBinary Model.Spec.sub x y) = _
  simp [Configured.Family.toModel, ExecFloat.Binary.toModel]

theorem isFinite_sub_binary64 (a b : Binary64) (ha : ExecFloat.Binary.isFinite a = true)
    (hb : ExecFloat.Binary.isFinite b = true)
    (hbound : |Model.toReal (ExecFloat.Binary.toModel a)| + |Model.toReal (ExecFloat.Binary.toModel b)| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    ExecFloat.Binary.isFinite (a - b) = true := by
  change Model.isFinite (ExecFloat.Binary.toModel (a - b)) = true
  rw [toModel_sub_binary64, ← Model.Proof.sub_eq_spec]
  exact Model.isFinite_sub_of_abs_add_le_posMaxFinite _ _ (by rfl) ha hb hbound

/-- A native float and a FloatLib binary64 value agree when both are finite with the same real value. -/
structure Agree (x : Float) (b : Binary64) : Prop where
  nfin : x.isFinite = true
  bfin : ExecFloat.Binary.isFinite b = true
  real : nreal x = breal b

theorem ofFloat_isFinite' {x : Float} (hx : x.isFinite = true) :
    ExecFloat.Binary.isFinite (ExecFloat.Binary.ofFloat x) = true := by
  rw [ofFloat_isFinite]; exact hx

theorem native_lt_iff_real (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x < y ↔ nreal x < nreal y := by
  rw [native_lt_iff x y hx hy]
  exact compareLess_iff_toReal_lt_binary64 _ _ (ofFloat_isFinite' hx) (ofFloat_isFinite' hy)

theorem binary_lt_iff_real (a b : Binary64) (ha : ExecFloat.Binary.isFinite a = true)
    (hb : ExecFloat.Binary.isFinite b = true) : a < b ↔ breal a < breal b :=
  compareLess_iff_toReal_lt_binary64 a b ha hb

theorem binary_le_iff_real (a b : Binary64) (ha : ExecFloat.Binary.isFinite a = true)
    (hb : ExecFloat.Binary.isFinite b = true) : a ≤ b ↔ breal a ≤ breal b := by
  constructor
  · intro h
    exact toReal_ge_of_ge_binary64 b a hb ha h
  · intro h
    exact ge_of_toReal_ge b a hb ha h

theorem native_le_iff_real (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x ≤ y ↔ nreal x ≤ nreal y := by
  rw [native_le_iff x y hx hy]
  exact binary_le_iff_real _ _ (ofFloat_isFinite' hx) (ofFloat_isFinite' hy)

theorem Agree.lt_iff {x y : Float} {a b : Binary64} (hxa : Agree x a) (hyb : Agree y b) :
    x < y ↔ a < b := by
  rw [native_lt_iff_real x y hxa.nfin hyb.nfin, binary_lt_iff_real a b hxa.bfin hyb.bfin,
    hxa.real, hyb.real]

theorem Agree.le_iff {x y : Float} {a b : Binary64} (hxa : Agree x a) (hyb : Agree y b) :
    x ≤ y ↔ a ≤ b := by
  rw [native_le_iff_real x y hxa.nfin hyb.nfin, binary_le_iff_real a b hxa.bfin hyb.bfin,
    hxa.real, hyb.real]

theorem Agree.sub {x y : Float} {a b : Binary64} (hxa : Agree x a) (hyb : Agree y b)
    (hbound : |breal a| + |breal b| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    Agree (x - y) (a - b) ∧ breal (a - b) = Model.roundAt FloatFormat.binary64 (breal a - breal b) := by
  have hsubN := ExecFloat.Binary.ofFloat_sub_of_isFinite x y hxa.nfin hyb.nfin
  have hfx := ofFloat_isFinite' hxa.nfin
  have hfy := ofFloat_isFinite' hyb.nfin
  have hboundN : |nreal x| + |nreal y| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
    rw [hxa.real, hyb.real]; exact hbound
  have hrealN : nreal (x - y) = Model.roundAt FloatFormat.binary64 (nreal x - nreal y) := by
    unfold nreal
    rw [hsubN]
    exact toReal_sub_eq_roundAt_binary64 _ _ hfx hfy hboundN
  have hrealB : breal (a - b) = Model.roundAt FloatFormat.binary64 (breal a - breal b) :=
    toReal_sub_eq_roundAt_binary64 a b hxa.bfin hyb.bfin hbound
  have hfinB : ExecFloat.Binary.isFinite (a - b) = true :=
    isFinite_sub_binary64 a b hxa.bfin hyb.bfin hbound
  have hfinN : (x - y).isFinite = true := by
    rw [← ofFloat_isFinite, hsubN]
    exact isFinite_sub_binary64 _ _ hfx hfy hboundN
  refine ⟨⟨hfinN, hfinB, ?_⟩, hrealB⟩
  rw [hrealN, hrealB, hxa.real, hyb.real]

theorem Agree.mul {x y : Float} {a b : Binary64} (hxa : Agree x a) (hyb : Agree y b)
    (hbound : |breal a| * |breal b| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    Agree (x * y) (a * b) ∧ breal (a * b) = Model.roundAt FloatFormat.binary64 (breal a * breal b) := by
  have hmulN := ofFloat_mul_of_isFinite x y hxa.nfin hyb.nfin
  have hfx := ofFloat_isFinite' hxa.nfin
  have hfy := ofFloat_isFinite' hyb.nfin
  have hboundN : |nreal x| * |nreal y| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
    rw [hxa.real, hyb.real]; exact hbound
  have hrealN : nreal (x * y) = Model.roundAt FloatFormat.binary64 (nreal x * nreal y) := by
    unfold nreal
    rw [hmulN]
    exact toReal_mul_eq_roundAt_binary64 _ _ hfx hfy hboundN
  have hrealB : breal (a * b) = Model.roundAt FloatFormat.binary64 (breal a * breal b) :=
    toReal_mul_eq_roundAt_binary64 a b hxa.bfin hyb.bfin hbound
  have hfinB : ExecFloat.Binary.isFinite (a * b) = true := isFinite_mul_binary64 a b hxa.bfin hyb.bfin hbound
  have hfinN : (x * y).isFinite = true := by
    rw [← ofFloat_isFinite, hmulN]
    exact isFinite_mul_binary64 _ _ hfx hfy hboundN
  refine ⟨⟨hfinN, hfinB, ?_⟩, hrealB⟩
  rw [hrealN, hrealB, hxa.real, hyb.real]

theorem Agree.absFloat {x : Float} {a : Binary64} (hxa : Agree x a) :
    Agree (absFloat x) (ExecFloat.Binary.abs a) ∧ breal (ExecFloat.Binary.abs a) = |breal a| := by
  have hrealB : breal (ExecFloat.Binary.abs a) = |breal a| := by
    unfold breal
    rw [ExecFloat.Binary.toModel_abs, toReal_abs _ (by rfl) hxa.bfin]
  have hfinB : ExecFloat.Binary.isFinite (ExecFloat.Binary.abs a) = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.abs a)) = true
    rw [ExecFloat.Binary.toModel_abs, Model.isFinite_abs]
    exact hxa.bfin
  have hzero : Agree 0.0 (0.0 : Binary64) := by
    refine ⟨rfl, binary64_zero_isFinite, ?_⟩
    rw [nreal_eq, native_zero_unpack, unpackedToReal_zero]
    exact binary64_zero_toReal.symm
  refine ⟨⟨?_, hfinB, ?_⟩, hrealB⟩
  · unfold Geometry.absFloat
    split
    · exact (native_neg x hxa.nfin).1
    · exact hxa.nfin
  · rw [hrealB]
    unfold Geometry.absFloat
    split
    · rename_i hlt
      have hlt' := (native_lt_iff_real x 0.0 hxa.nfin hzero.nfin).mp hlt
      rw [hzero.real, show breal (0.0 : Binary64) = 0 from binary64_zero_toReal] at hlt'
      rw [nreal_eq, (native_neg x hxa.nfin).2, ← nreal_eq, hxa.real, abs_of_neg (hxa.real ▸ hlt')]
    · rename_i hge
      have hge' : ¬ nreal x < 0 := by
        intro h
        apply hge
        rw [native_lt_iff_real x 0.0 hxa.nfin hzero.nfin, hzero.real]
        rw [show breal (0.0 : Binary64) = 0 from binary64_zero_toReal]
        exact h
      rw [hxa.real] at hge' ⊢
      exact (abs_of_nonneg (not_lt.mp hge')).symm

theorem Agree.zero : Agree 0.0 (0.0 : Binary64) := by
  refine ⟨rfl, binary64_zero_isFinite, ?_⟩
  rw [nreal_eq, native_zero_unpack, unpackedToReal_zero]
  exact binary64_zero_toReal.symm

theorem Agree.int32 (n : Int32) (hn : |n.toInt| ≤ (mainCoordBoundNat : ℤ) + 2) :
    Agree n.toFloat (intToBinary64 n.toInt) ∧ breal (intToBinary64 n.toInt) = (n.toInt : ℝ) := by
  have hb := ofFloat_int32ToFloat n
  have hfin := intToBinary64_isFinite n.toInt hn
  refine ⟨⟨?_, hfin, by unfold nreal; rw [hb]; rfl⟩, intToBinary64_toReal_eq n.toInt hn⟩
  rw [← ofFloat_isFinite, hb]
  exact hfin

end Geometry

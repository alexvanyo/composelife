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

import models.EasingPiecewiseModel

namespace UiCommon.Model

/-! ### `floatCompare` Order Properties -/

theorem floatCompare_trichotomy (a b : Float32) :
    floatCompare a b = -1 ∨ floatCompare a b = 0 ∨ floatCompare a b = 1 := by
  unfold floatCompare
  by_cases hab : a < b
  · simp [hab]
  · by_cases hba : b < a
    · simp [hab, hba]
    · simp only [hab, hba, ↓reduceIte]
      by_cases h1 : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 <
          (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32
      · simp [h1]
      · by_cases h2 : (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32 <
            (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32
        · simp [h1, h2]
        · simp [h1, h2]

theorem floatCompare_gt_zero_iff_eq_one (a b : Float32) :
    floatCompare a b > 0 ↔ floatCompare a b = 1 := by
  rcases floatCompare_trichotomy a b with h | h | h <;> simp [h] <;> decide

theorem floatCompare_lt_zero_iff_eq_neg_one (a b : Float32) :
    floatCompare a b < 0 ↔ floatCompare a b = -1 := by
  rcases floatCompare_trichotomy a b with h | h | h <;> simp [h] <;> decide

private theorem unpackedFloat_compare_eq_lt_implies_gt (u1 u2 : Float.Model.UnpackedFloat)
    (h : u1.compare u2 = some .lt) : u2.compare u1 = some .gt := by
  cases u1 with
  | notANumber => simp [Float.Model.UnpackedFloat.compare] at h
  | infinity s1 =>
    cases u2 with
    | notANumber => simp [Float.Model.UnpackedFloat.compare] at h
    | infinity s2 =>
      cases s1 <;> cases s2 <;> simp [Float.Model.UnpackedFloat.compare, compare] at h ⊢
    | finite s2 m2 e2 p2 => cases s1 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
    | zero s2 => cases s1 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
  | zero s1 =>
    cases u2 with
    | notANumber => simp [Float.Model.UnpackedFloat.compare] at h
    | infinity s2 => cases s2 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
    | zero s2 => simp [Float.Model.UnpackedFloat.compare] at h
    | finite s2 m2 e2 p2 => cases s2 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
  | finite s1 m1 e1 p1 =>
    cases u2 with
    | notANumber => simp [Float.Model.UnpackedFloat.compare] at h
    | infinity s2 => cases s2 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
    | zero s2 => cases s1 <;> simp [Float.Model.UnpackedFloat.compare] at h ⊢
    | finite s2 m2 e2 p2 =>
      cases s1 with
      | negative =>
        cases s2 with
        | negative =>
          simp only [Float.Model.UnpackedFloat.compare] at h ⊢
          have he : compare e1 e2 = .gt ∨ (compare e1 e2 = .eq ∧ compare m1 m2 = .gt) := by
            cases hce : compare e1 e2 <;> cases hcm : compare m1 m2 <;>
              simp [hce, hcm, Ordering.then, Ordering.swap] at h <;> simp
          rcases he with he | ⟨he, hm⟩
          · have he' : compare e2 e1 = .lt := by
              simp only [compare, compareOfLessAndEq] at he ⊢
              split at he <;> try contradiction
              split at he <;> try contradiction
              rename_i hne hgt
              have hlt : e2 < e1 := by omega
              simp [hlt]
            simp [he', Ordering.then, Ordering.swap]
          · have he' : compare e2 e1 = .eq := by
              simp only [compare, compareOfLessAndEq] at he ⊢
              split at he <;> try contradiction
              split at he <;> try contradiction
              rename_i h1 h2
              have heq : e1 = e2 := by omega
              subst heq; simp
            have hm' : compare m2 m1 = .lt := by
              simp only [compare, compareOfLessAndEq] at hm ⊢
              split at hm <;> try contradiction
              split at hm <;> try contradiction
              rename_i hne hgt
              have hlt : m2 < m1 := by omega
              simp [hlt]
            simp [he', hm', Ordering.then, Ordering.swap]
        | positive =>
          simp [Float.Model.UnpackedFloat.compare] at h ⊢
      | positive =>
        cases s2 with
        | negative =>
          simp [Float.Model.UnpackedFloat.compare] at h
        | positive =>
          simp only [Float.Model.UnpackedFloat.compare] at h ⊢
          have he : compare e1 e2 = .lt ∨ (compare e1 e2 = .eq ∧ compare m1 m2 = .lt) := by
            cases hce : compare e1 e2 <;> cases hcm : compare m1 m2 <;>
              simp [hce, hcm, Ordering.then] at h <;> simp
          rcases he with he | ⟨he, hm⟩
          · have he' : compare e2 e1 = .gt := by
              simp only [compare, compareOfLessAndEq] at he ⊢
              split at he
              · rename_i hlt
                have hnlt : ¬ (e2 < e1) := by omega
                have hne : ¬ (e2 = e1) := by omega
                simp [hnlt, hne]
              · split at he <;> contradiction
            simp [he', Ordering.then]
          · have he' : compare e2 e1 = .eq := by
              simp only [compare, compareOfLessAndEq] at he ⊢
              split at he <;> try contradiction
              split at he <;> try contradiction
              rename_i h1 h2
              have heq : e1 = e2 := by omega
              subst heq; simp
            have hm' : compare m2 m1 = .gt := by
              simp only [compare, compareOfLessAndEq] at hm ⊢
              split at hm
              · rename_i hlt
                have hnlt : ¬ (m2 < m1) := by omega
                have hne : ¬ (m2 = m1) := by omega
                simp [hnlt, hne]
              · split at hm <;> contradiction
            simp [he', hm', Ordering.then]

private theorem floatCompare_both_lt_absurd (a b : Float32) :
    ¬ (a < b ∧ b < a) := by
  rintro ⟨hab, hba⟩
  have h1m : a.toModel.lt b.toModel = true := of_decide_eq_true hab
  have h2m : b.toModel.lt a.toModel = true := of_decide_eq_true hba
  have h1 : a.toModel.unpack.compare b.toModel.unpack = some .lt := by
    simpa [Float32.Model.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt] using h1m
  have h2 : b.toModel.unpack.compare a.toModel.unpack = some .lt := by
    simpa [Float32.Model.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt] using h2m
  have hgt := unpackedFloat_compare_eq_lt_implies_gt _ _ h1
  rw [h2] at hgt
  contradiction

theorem floatCompare_gt_zero_iff_flip_lt_zero (a b : Float32) :
    floatCompare a b > 0 ↔ floatCompare b a < 0 := by
  constructor
  · intro h
    have h1 : floatCompare a b = 1 := (floatCompare_gt_zero_iff_eq_one a b).mp h
    unfold floatCompare at h1 ⊢
    by_cases hab : a < b
    · simp [hab] at h1
    · by_cases hba : b < a
      · simp [hba]
      · simp only [hab, hba, ↓reduceIte] at h1 ⊢
        by_cases hlt1 : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 <
            (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32
        · simp [hlt1] at h1
        · by_cases hlt2 : (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32 <
              (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32
          · simp [hlt2]
          · simp [hlt1, hlt2] at h1
  · intro h
    have h1 : floatCompare b a = -1 := (floatCompare_lt_zero_iff_eq_neg_one b a).mp h
    unfold floatCompare at h1 ⊢
    by_cases hba : b < a
    · have hnab : ¬ (a < b) := fun hab => floatCompare_both_lt_absurd a b ⟨hab, hba⟩
      simp [hnab, hba]
    · by_cases hab : a < b
      · simp [hba, hab] at h1
      · simp only [hba, hab, ↓reduceIte] at h1 ⊢
        by_cases hlt : (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32 <
            (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32
        · have hn : ¬ ((if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 <
              (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32) :=
            Int32.lt_asymm hlt
          simp [hn, hlt]
        · simp only [hlt, ↓reduceIte] at h1 ⊢
          by_cases hlt2 : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 <
              (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32
          · simp [hlt2] at h1
          · simp [hlt2] at h1

theorem floatCompare_lt_zero_iff_flip_gt_zero (a b : Float32) :
    floatCompare a b < 0 ↔ floatCompare b a > 0 :=
  (floatCompare_gt_zero_iff_flip_lt_zero b a).symm

theorem floatCompare_not_le_iff_gt (a b : Float32) :
    (¬ floatCompare a b ≤ 0) ↔ floatCompare a b > 0 := by
  rcases floatCompare_trichotomy a b with h | h | h <;> simp [h] <;> decide

theorem floatCompare_eq_zero_implies_floatKeyEq (a b : Float32)
    (h : floatCompare a b = 0) : floatKeyEq a b = true := by
  unfold floatCompare at h
  by_cases hab : a < b
  · simp [hab] at h
  · by_cases hba : b < a
    · simp [hab, hba] at h
    · simp only [hab, hba, ↓reduceIte] at h
      by_cases h1 : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 <
          (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32
      · simp [h1] at h
      · by_cases h2 : (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32 <
            (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32
        · simp [h1, h2] at h
        · have heq : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32 =
              (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32 :=
            Int32.le_antisymm (Int32.not_lt.mp h2) (Int32.not_lt.mp h1)
          have heqU : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits) =
              (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits) := by
            have := congrArg Int32.toUInt32 heq
            simpa using this
          unfold floatKeyEq
          exact beq_iff_eq.mpr heqU

private theorem float32_toBits_0x7fc00000_isNaN (a : Float32) (hb : a.toBits = 0x7fc00000) :
    a.isNaN = true := by
  have h : a = Float32.ofBits 0x7fc00000 := by
    cases a with | ofModel m =>
    cases m with | mk bits val =>
    simp [Float32.toBits] at hb
    subst hb
    rfl
  rw [h]
  decide

theorem floatCompareLt_implies_not_floatKeyEq (a b : Float32)
    (h : floatCompareLt a b = true) : floatKeyEq a b = false := by
  unfold floatCompareLt at h
  have hlt : floatCompare a b < 0 := decide_eq_true_eq.mp h
  have hne : floatCompare a b ≠ 0 := by intro heq; rw [heq] at hlt; contradiction
  by_cases hkey : floatKeyEq a b = true
  · exfalso
    have hkeyTrue : floatKeyEq a b = true := hkey
    unfold floatKeyEq at hkeyTrue
    have hbits : (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits) =
        (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits) := beq_iff_eq.mp hkeyTrue
    have hnlt_ab : ¬ (a < b) := by
      by_cases ha : a.isNaN
      · intro hltab
        have hltm : a.toModel.lt b.toModel = true := of_decide_eq_true hltab
        have hcmp : a.toModel.unpack.compare b.toModel.unpack = some .lt := by
          simpa [Float32.Model.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt] using hltm
        have hau : a.toModel.unpack = .notANumber := by
          cases hu : a.toModel.unpack <;> simp [Float32.isNaN, Float32.Model.isNaN, Float.Model.UnpackedFloat.isNaN, hu] at ha ⊢
        rw [hau] at hcmp
        simp [Float.Model.UnpackedFloat.compare] at hcmp
      · have hb : b.isNaN = false := by
          by_cases hb' : b.isNaN = true
          · simp [ha, hb'] at hbits
            have haNaN : a.isNaN = true := float32_toBits_0x7fc00000_isNaN a hbits
            exact absurd haNaN ha
          · exact Bool.eq_false_iff.mpr hb'
        simp [ha, hb] at hbits
        have heqab : a = b := by
          cases a with | ofModel am =>
          cases b with | ofModel bm =>
          congr 1; cases am; cases bm
          simp only [Float32.toBits] at hbits
          subst hbits; rfl
        subst heqab
        exact fun hlt => floatCompare_both_lt_absurd a a ⟨hlt, hlt⟩
    have hnlt_ba : ¬ (b < a) := by
      by_cases hb : b.isNaN
      · intro hltba
        have hltm : b.toModel.lt a.toModel = true := of_decide_eq_true hltba
        have hcmp : b.toModel.unpack.compare a.toModel.unpack = some .lt := by
          simpa [Float32.Model.lt, Float.Model.lt, Float.Model.UnpackedFloat.lt] using hltm
        have hbu : b.toModel.unpack = .notANumber := by
          cases hu : b.toModel.unpack <;> simp [Float32.isNaN, Float32.Model.isNaN, Float.Model.UnpackedFloat.isNaN, hu] at hb ⊢
        rw [hbu] at hcmp
        simp [Float.Model.UnpackedFloat.compare] at hcmp
      · have ha : a.isNaN = false := by
          by_cases ha' : a.isNaN = true
          · simp [ha', hb] at hbits
            have hbNaN : b.isNaN = true := float32_toBits_0x7fc00000_isNaN b hbits.symm
            exact absurd hbNaN hb
          · exact Bool.eq_false_iff.mpr ha'
        simp [ha, hb] at hbits
        have heqab : a = b := by
          cases a with | ofModel am =>
          cases b with | ofModel bm =>
          congr 1; cases am; cases bm
          simp only [Float32.toBits] at hbits
          subst hbits; rfl
        subst heqab
        exact fun hlt => floatCompare_both_lt_absurd a a ⟨hlt, hlt⟩
    unfold floatCompare at hne
    simp [hnlt_ab, hnlt_ba, hbits] at hne
  · exact Bool.eq_false_iff.mpr hkey

/-! ### Binary Search Termination, Bounds Safety, and Exact Specification -/

theorem floorBinarySearchLoop_readsInBounds_Impl (keys : List Float32) (value : Float32)
    (low high fuel : Nat) (hlo : low < high) (hhi : high ≤ keys.length) :
    FloorSearchReadsInBounds keys value low high fuel := by
  induction fuel generalizing low high with
  | zero => trivial
  | succ f ih =>
    unfold FloorSearchReadsInBounds
    split
    · next hcmp =>
      let mid := (low + high) / 2
      have hmid_lo : low < mid := by omega
      have hmid_hi : mid < high := by omega
      refine ⟨by omega, ?_⟩
      split
      · exact ih mid high hmid_hi hhi
      · exact ih low mid hmid_lo (by omega)
    · trivial

private theorem floorBinarySearchLoop_fuel_mono (keys : List Float32) (value : Float32)
    (low high fuel1 fuel2 : Nat) (hlo : low < high)
    (hf1 : high - low - 1 < 2 ^ fuel1) (hf2 : high - low - 1 < 2 ^ fuel2) :
    floorBinarySearchLoop keys value low high fuel1 =
      floorBinarySearchLoop keys value low high fuel2 := by
  induction fuel1 generalizing low high fuel2 with
  | zero =>
    have hd : high - low = 1 := by simp at hf1; omega
    have hstop : ¬(low + 1 < high) := by omega
    cases fuel2 with
    | zero => rfl
    | succ f2 =>
      unfold floorBinarySearchLoop
      simp [hstop]
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      have hd : high - low = 1 := by simp at hf2; omega
      have hstop : ¬(low + 1 < high) := by omega
      unfold floorBinarySearchLoop
      simp [hstop]
    | succ f2 =>
      unfold floorBinarySearchLoop
      by_cases hcmp : low + 1 < high
      · simp only [hcmp, ↓reduceIte]
        have hmid_lo : low < (low + high) / 2 := by omega
        have hmid_hi : (low + high) / 2 < high := by omega
        have hpow1 : 2 ^ (f1 + 1) = 2 * 2 ^ f1 := by rw [Nat.pow_succ]; omega
        have hpow2 : 2 ^ (f2 + 1) = 2 * 2 ^ f2 := by rw [Nat.pow_succ]; omega
        split
        · exact ih ((low + high) / 2) high f2 hmid_hi (by omega) (by omega)
        · exact ih low ((low + high) / 2) f2 hmid_lo (by omega) (by omega)
      · simp [hcmp]

theorem floorBinarySearchFuel_suffices (n : Nat) (hn : 0 < n) :
    n - 1 < 2 ^ (floorBinarySearchFuel n) := by
  unfold floorBinarySearchFuel
  have hlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  omega

theorem floorBinarySearchLoop_terminates_in_log_Impl (keys : List Float32) (value : Float32)
    (low high fuel : Nat) (hlo : low < high) (hhi : high ≤ keys.length)
    (hf : floorBinarySearchFuel keys.length ≤ fuel) :
    floorBinarySearchLoop keys value low high fuel =
      floorBinarySearchLoop keys value low high (floorBinarySearchFuel keys.length) := by
  have hk : 0 < keys.length := by omega
  have hpowBase : keys.length - 1 < 2 ^ (floorBinarySearchFuel keys.length) :=
    floorBinarySearchFuel_suffices keys.length hk
  have hpow1 : high - low - 1 < 2 ^ (floorBinarySearchFuel keys.length) := by omega
  have hpow2 : 2 ^ (floorBinarySearchFuel keys.length) ≤ 2 ^ fuel :=
    Nat.pow_le_pow_right (by decide) hf
  exact floorBinarySearchLoop_fuel_mono keys value low high fuel (floorBinarySearchFuel keys.length)
    hlo (by omega) hpow1

private theorem floorBinarySearchLoop_invariant (keys : List Float32) (value : Float32)
    (low high fuel : Nat) (hlo : low < high) (hhi : high ≤ keys.length)
    (hf : high - low - 1 < 2 ^ fuel)
    (hle : floatCompare keys[low]! value ≤ 0)
    (hgt : ∀ _hlt : high < keys.length, floatCompare keys[high]! value > 0) :
    let r := floorBinarySearchLoop keys value low high fuel
    low ≤ r ∧ r < high ∧ floatCompare keys[r]! value ≤ 0 ∧
      (r + 1 = keys.length ∨ (r + 1 < keys.length ∧ floatCompare keys[r + 1]! value > 0)) := by
  induction fuel generalizing low high with
  | zero =>
    have hd : high - low = 1 := by simp at hf; omega
    unfold floorBinarySearchLoop
    refine ⟨Nat.le_refl _, hlo, hle, ?_⟩
    by_cases hheq : high = keys.length
    · left; omega
    · right
      have hlt : high < keys.length := by omega
      refine ⟨by omega, ?_⟩
      simpa [show low + 1 = high by omega] using hgt hlt
  | succ f ih =>
    unfold floorBinarySearchLoop
    by_cases hcmp : low + 1 < high
    · simp only [hcmp, ↓reduceIte]
      have hmid_lo : low < (low + high) / 2 := by omega
      have hmid_hi : (low + high) / 2 < high := by omega
      have hpow : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ]; omega
      by_cases hmidle : floatCompare keys[(low + high) / 2]! value ≤ 0
      · simp only [hmidle, ↓reduceIte]
        have hres := ih ((low + high) / 2) high hmid_hi hhi (by omega) hmidle hgt
        exact ⟨by omega, hres.2.1, hres.2.2.1, hres.2.2.2⟩
      · simp only [hmidle, ↓reduceIte]
        have hmidgt : floatCompare keys[(low + high) / 2]! value > 0 :=
          (floatCompare_not_le_iff_gt _ _).mp hmidle
        have hgt' : ∀ _hlt : (low + high) / 2 < keys.length,
            floatCompare keys[(low + high) / 2]! value > 0 := fun _ => hmidgt
        have hres := ih low ((low + high) / 2) hmid_lo (by omega) (by omega) hle hgt'
        exact ⟨hres.1, by omega, hres.2.2.1, hres.2.2.2⟩
    · simp only [hcmp, ↓reduceIte]
      have hd : high = low + 1 := by omega
      refine ⟨Nat.le_refl _, hlo, hle, ?_⟩
      by_cases hheq : high = keys.length
      · left; omega
      · right
        have hlt : high < keys.length := by omega
        refine ⟨by omega, ?_⟩
        simpa [hd] using hgt hlt

theorem floorBinarySearch_neg_one_iff_Impl (keys : List Float32) (value : Float32)
    (hne : 0 < keys.length) :
    floorBinarySearch keys value = -1 ↔ floatCompare value keys[0] < 0 := by
  unfold floorBinarySearch
  have hnz : keys.length ≠ 0 := by omega
  simp only [hnz, ↓reduceDIte]
  rw [← floatCompare_gt_zero_iff_flip_lt_zero]
  by_cases hgt : floatCompare keys[0] value > 0
  · simp [hgt]
  · simp only [hgt, ↓reduceIte]
    constructor
    · intro heq; omega
    · intro h; exact False.elim h

theorem floorBinarySearch_nonneg_bounds_Impl (keys : List Float32) (value : Float32)
    (hne : 0 < keys.length) (hge : ¬ floatCompare value keys[0] < 0) :
    ∃ i : Nat,
      floorBinarySearch keys value = (i : Int) ∧
      i < keys.length ∧
      floatCompare keys[i]! value ≤ 0 ∧
      (i + 1 = keys.length ∨ (i + 1 < keys.length ∧ floatCompare value keys[i + 1]! < 0)) := by
  have hnotgt : ¬ floatCompare keys[0] value > 0 := by
    rw [floatCompare_gt_zero_iff_flip_lt_zero]
    exact hge
  have hle0 : floatCompare keys[0]! value ≤ 0 := by
    have h1 : keys[0]! = keys[0] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hne]
    rw [h1]
    exact (Classical.not_not.mp fun h => hnotgt ((floatCompare_not_le_iff_gt _ _).mp h))
  have hinv := floorBinarySearchLoop_invariant keys value 0 keys.length
    (floorBinarySearchFuel keys.length) hne (Nat.le_refl _)
    (floorBinarySearchFuel_suffices keys.length hne) hle0
    (fun h => absurd h (Nat.lt_irrefl _))
  refine ⟨floorBinarySearchLoop keys value 0 keys.length (floorBinarySearchFuel keys.length),
    ?_, hinv.2.1, hinv.2.2.1, ?_⟩
  · unfold floorBinarySearch
    have hnz : keys.length ≠ 0 := by omega
    simp [hnz, hnotgt]
  · rcases hinv.2.2.2 with heq | ⟨hlt, hgt⟩
    · exact Or.inl heq
    · exact Or.inr ⟨hlt, (floatCompare_gt_zero_iff_flip_lt_zero _ _).mp hgt⟩

/-! ### Keyframe Validation & Nonzero Denominator Proofs -/

private theorem putKeyMap_length_le {E : Type} (m : List (Float32 × E)) (k : Float32) (e : E) :
    (putKeyMap m k e).length ≤ m.length + 1 := by
  induction m with
  | nil => simp [putKeyMap]
  | cons hd tl ih =>
    rcases hd with ⟨k0, e0⟩
    unfold putKeyMap
    split <;> simp <;> omega

private theorem putKeyMap_length_eq_succ_iff {E : Type}
    (m : List (Float32 × E)) (k : Float32) (e : E) :
    (putKeyMap m k e).length = m.length + 1 ↔ ∀ k0 ∈ m.map Prod.fst, floatKeyEq k0 k = false := by
  induction m with
  | nil => simp [putKeyMap]
  | cons hd tl ih =>
    rcases hd with ⟨k0, e0⟩
    unfold putKeyMap
    by_cases h : floatKeyEq k0 k = true
    · simp [h]
    · have hf : floatKeyEq k0 k = false := Bool.eq_false_iff.mpr h
      simp [hf, ih]

private theorem buildKeyframeMap_length_le {E : Type}
    (acc : List (Float32 × E)) (xs : List (Float32 × E)) :
    (xs.foldl (fun m p => putKeyMap m p.1 p.2) acc).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨k, e⟩
    simp only [List.foldl_cons]
    have h1 := ih (putKeyMap acc k e)
    have h2 := putKeyMap_length_le acc k e
    simp only [List.length_cons]
    omega

private theorem putKeyMap_keys_fresh {E : Type} (m : List (Float32 × E)) (k : Float32) (e : E)
    (hf : ∀ k0 ∈ m.map Prod.fst, floatKeyEq k0 k = false) :
    (putKeyMap m k e).map Prod.fst = m.map Prod.fst ++ [k] := by
  induction m with
  | nil => simp [putKeyMap]
  | cons hd tl ih =>
    rcases hd with ⟨k0, e0⟩
    have h0 : floatKeyEq k0 k = false := hf k0 (by simp)
    have htl : ∀ k1 ∈ tl.map Prod.fst, floatKeyEq k1 k = false :=
      fun k1 hk1 => hf k1 (by simp [hk1])
    simp [putKeyMap, h0, ih htl]

private theorem putKeyMap_vals_fresh {E : Type} (m : List (Float32 × E)) (k : Float32) (e : E)
    (hf : ∀ k0 ∈ m.map Prod.fst, floatKeyEq k0 k = false) :
    (putKeyMap m k e).map Prod.snd = m.map Prod.snd ++ [e] := by
  induction m with
  | nil => simp [putKeyMap]
  | cons hd tl ih =>
    rcases hd with ⟨k0, e0⟩
    have h0 : floatKeyEq k0 k = false := hf k0 (by simp)
    have htl : ∀ k1 ∈ tl.map Prod.fst, floatKeyEq k1 k = false :=
      fun k1 hk1 => hf k1 (by simp [hk1])
    simp [putKeyMap, h0, ih htl]

private theorem buildKeyframeMap_full_length_spec {E : Type}
    (acc : List (Float32 × E)) (xs : List (Float32 × E))
    (hlen : (xs.foldl (fun m p => putKeyMap m p.1 p.2) acc).length = acc.length + xs.length) :
    (xs.foldl (fun m p => putKeyMap m p.1 p.2) acc).map Prod.fst =
      acc.map Prod.fst ++ xs.map Prod.fst ∧
    (xs.foldl (fun m p => putKeyMap m p.1 p.2) acc).map Prod.snd =
      acc.map Prod.snd ++ xs.map Prod.snd ∧
    (∀ k ∈ xs.map Prod.fst, ∀ k0 ∈ acc.map Prod.fst, floatKeyEq k0 k = false) ∧
    List.Pairwise (fun a b => floatKeyEq a b = false) (xs.map Prod.fst) := by
  induction xs generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨k, e⟩
    simp only [List.foldl_cons, List.length_cons] at hlen ⊢
    have htail : (tl.foldl (fun m p => putKeyMap m p.1 p.2) (putKeyMap acc k e)).length ≤
        (putKeyMap acc k e).length + tl.length := buildKeyframeMap_length_le (putKeyMap acc k e) tl
    have hput : (putKeyMap acc k e).length ≤ acc.length + 1 := putKeyMap_length_le acc k e
    have hputEq : (putKeyMap acc k e).length = acc.length + 1 := by omega
    have htailEq : (tl.foldl (fun m p => putKeyMap m p.1 p.2) (putKeyMap acc k e)).length =
        (putKeyMap acc k e).length + tl.length := by omega
    have hfresh := (putKeyMap_length_eq_succ_iff acc k e).mp hputEq
    rcases ih (putKeyMap acc k e) htailEq with ⟨hk, hv, hacc, hpw⟩
    have hkeys : (putKeyMap acc k e).map Prod.fst = acc.map Prod.fst ++ [k] :=
      putKeyMap_keys_fresh acc k e hfresh
    have hvals : (putKeyMap acc k e).map Prod.snd = acc.map Prod.snd ++ [e] :=
      putKeyMap_vals_fresh acc k e hfresh
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hk, hkeys]; simp
    · rw [hv, hvals]; simp
    · intro x hx k0 hk0
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hxtl
      · exact hfresh k0 hk0
      · exact hacc x hxtl k0 (by rw [hkeys]; simp [hk0])
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, hpw⟩
      exact hacc x hx k (by rw [hkeys]; simp)

private theorem isSortedByKeyframe_strict_of_pairwise {E : Type}
    (xs : List (Float32 × E))
    (hsort : isSortedByKeyframe xs = true)
    (hpw : List.Pairwise (fun a b => floatKeyEq a b = false) (xs.map Prod.fst)) :
    KeysStrictlyIncreasing (xs.map Prod.fst) := by
  induction xs with
  | nil => trivial
  | cons hd tl ih =>
    rcases hd with ⟨k1, e1⟩
    cases tl with
    | nil => trivial
    | cons hd2 tl2 =>
      rcases hd2 with ⟨k2, e2⟩
      simp only [isSortedByKeyframe, Bool.and_eq_true] at hsort
      cases hpw with
      | cons hpw1 hpw2 =>
        have hk12_ne : floatKeyEq k1 k2 = false := hpw1 k2 (by simp)
        have hle : floatCompare k1 k2 ≤ 0 := by
          have hd := hsort.1
          unfold floatCompareLe at hd
          exact decide_eq_true_eq.mp hd
        have hne0 : floatCompare k1 k2 ≠ 0 := fun h0 => by
          have := floatCompare_eq_zero_implies_floatKeyEq k1 k2 h0
          rw [hk12_ne] at this
          contradiction
        have hlt : floatCompareLt k1 k2 = true := by
          unfold floatCompareLt
          have hltI : floatCompare k1 k2 < 0 := by
            rcases floatCompare_trichotomy k1 k2 with hc | hc | hc
            · rw [hc]; decide
            · exact absurd hc hne0
            · rw [hc] at hle; contradiction
          exact decide_eq_true hltI
        exact ⟨hlt, ih hsort.2 hpw2⟩

theorem validateEasingKeyframes_strict_increasing_Impl {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E)
    (hval : validateEasingKeyframes easing easings = some (keys, es)) :
    keys = (0.0 : Float32) :: easings.map Prod.fst ∧
      es = easing :: easings.map Prod.snd ∧
      keys.length = es.length ∧
      0 < keys.length ∧
      KeysStrictlyIncreasing (easings.map Prod.fst) ∧
      (∀ k ∈ easings.map Prod.fst, floatKeyEq (0.0 : Float32) k = false) := by
  unfold validateEasingKeyframes at hval
  by_cases hsort : isSortedByKeyframe easings = true
  · simp only [hsort, ↓reduceIte] at hval
    by_cases hlen : (buildKeyframeMap easing easings).length == easings.length + 1
    · simp only [hlen, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hval
      rcases hval with ⟨rfl, rfl⟩
      have hlenEq : (buildKeyframeMap easing easings).length =
          [((0.0 : Float32), easing)].length + easings.length := by
        simpa [Nat.add_comm] using beq_iff_eq.mp hlen
      rcases buildKeyframeMap_full_length_spec [((0.0 : Float32), easing)] easings hlenEq with
        ⟨hk, hv, hfresh0, hpw⟩
      unfold buildKeyframeMap
      refine ⟨hk, hv, ?_, ?_, ?_, ?_⟩
      · rw [hk, hv]; simp
      · rw [hk]; simp
      · exact isSortedByKeyframe_strict_of_pairwise easings hsort hpw
      · intro k hkMem
        exact hfresh0 k hkMem (0.0 : Float32) (by simp)
    · simp [hlen] at hval
  · simp [hsort] at hval

private theorem keysStrictlyIncreasing_adj (keys : List Float32)
    (hstrict : KeysStrictlyIncreasing keys) (i : Nat) (hlt : i + 1 < keys.length) :
    floatCompareLt keys[i]! keys[i + 1]! = true := by
  induction keys generalizing i with
  | nil => simp at hlt
  | cons a tl ih =>
    cases tl with
    | nil => simp at hlt
    | cons b rest =>
      cases i with
      | zero => exact hstrict.1
      | succ j =>
        exact ih hstrict.2 j (by simpa using hlt)

theorem piecewiseSegment_valid_nonzero_denom_Impl {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E) (t : Float32)
    (hval : validateEasingKeyframes easing easings = some (keys, es))
    (hunitInterval : ∀ k ∈ easings.map Prod.fst,
      floatCompareLt (0.0 : Float32) k = true ∧ floatCompareLt k (1.0 : Float32) = true)
    (ht : floatCompare (0.0 : Float32) t ≤ 0) :
    ∃ e pStart pEnd,
      piecewiseSegment keys es t = some (e, pStart, pEnd) ∧
      floatCompareLt pStart pEnd = true ∧
      floatKeyEq pStart pEnd = false := by
  rcases validateEasingKeyframes_strict_increasing_Impl easing easings keys es hval with
    ⟨rfl, rfl, _, hpos, hstrictTail, _⟩
  have hstrict : KeysStrictlyIncreasing ((0.0 : Float32) :: easings.map Prod.fst) := by
    cases hxs : easings.map Prod.fst with
    | nil =>
      change KeysStrictlyIncreasing [(0.0 : Float32)]
      trivial
    | cons k1 tail =>
      change KeysStrictlyIncreasing ((0.0 : Float32) :: k1 :: tail)
      refine ⟨?_, ?_⟩
      · exact (hunitInterval k1 (by rw [hxs]; simp)).1
      · simpa [hxs] using hstrictTail
  have hnotlt0 : ¬ floatCompare t ((0.0 : Float32) :: easings.map Prod.fst)[0] < 0 := by
    intro hlt
    have hgt : floatCompare (0.0 : Float32) t > 0 :=
      (floatCompare_lt_zero_iff_flip_gt_zero _ _).mp hlt
    exact Int32.not_le.mpr hgt ht
  rcases floorBinarySearch_nonneg_bounds_Impl ((0.0 : Float32) :: easings.map Prod.fst) t hpos hnotlt0 with
    ⟨i, hidx, hilt, _, hnext⟩
  have hilt' : i < (easing :: easings.map Prod.snd).length := by
    simp only [List.length_cons, List.length_map] at hilt ⊢; exact hilt
  have hgetK : ((0.0 : Float32) :: easings.map Prod.fst)[i]? =
      some ((0.0 : Float32) :: easings.map Prod.fst)[i] := List.getElem?_eq_getElem hilt
  have hgetE : (easing :: easings.map Prod.snd)[i]? =
      some (easing :: easings.map Prod.snd)[i] := List.getElem?_eq_getElem hilt'
  have hnonneg : ¬ ((i : Int) < 0) := by omega
  have hseg : piecewiseSegment ((0.0 : Float32) :: easings.map Prod.fst) (easing :: easings.map Prod.snd) t =
      some ((easing :: easings.map Prod.snd)[i], ((0.0 : Float32) :: easings.map Prod.fst)[i],
        (((0.0 : Float32) :: easings.map Prod.fst)[i + 1]?.getD (1.0 : Float32))) := by
    unfold piecewiseSegment
    rw [hidx]
    simp [hnonneg, hgetK, hgetE]
  refine ⟨(easing :: easings.map Prod.snd)[i], ((0.0 : Float32) :: easings.map Prod.fst)[i],
    (((0.0 : Float32) :: easings.map Prod.fst)[i + 1]?.getD (1.0 : Float32)), hseg, ?_, ?_⟩
  · rcases hnext with heqLen | ⟨hltNext, _⟩
    · have hnone : ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]? = none :=
        List.getElem?_eq_none (by simp only [List.length_cons, List.length_map] at heqLen ⊢; omega)
      simp only [hnone, Option.getD_none]
      cases i with
      | zero =>
        change floatCompareLt (0.0 : Float32) (1.0 : Float32) = true
        decide
      | succ j =>
        have hjlt : j < (easings.map Prod.fst).length := by simpa using hilt
        have hmem : (easings.map Prod.fst)[j] ∈ easings.map Prod.fst := List.getElem_mem hjlt
        exact (hunitInterval _ hmem).2
    · have hgetNext : ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]? =
          some ((0.0 : Float32) :: easings.map Prod.fst)[i + 1] := List.getElem?_eq_getElem hltNext
      simp only [hgetNext, Option.getD_some]
      have hadj := keysStrictlyIncreasing_adj ((0.0 : Float32) :: easings.map Prod.fst) hstrict i hltNext
      simpa [List.getElem!_eq_getElem?_getD, hgetK, hgetNext] using hadj
  · apply floatCompareLt_implies_not_floatKeyEq
    rcases hnext with heqLen | ⟨hltNext, _⟩
    · have hnone : ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]? = none :=
        List.getElem?_eq_none (by simp only [List.length_cons, List.length_map] at heqLen ⊢; omega)
      simp only [hnone, Option.getD_none]
      cases i with
      | zero =>
        change floatCompareLt (0.0 : Float32) (1.0 : Float32) = true
        decide
      | succ j =>
        have hjlt : j < (easings.map Prod.fst).length := by simpa using hilt
        have hmem : (easings.map Prod.fst)[j] ∈ easings.map Prod.fst := List.getElem_mem hjlt
        exact (hunitInterval _ hmem).2
    · have hgetNext : ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]? =
          some ((0.0 : Float32) :: easings.map Prod.fst)[i + 1] := List.getElem?_eq_getElem hltNext
      simp only [hgetNext, Option.getD_some]
      have hadj := keysStrictlyIncreasing_adj ((0.0 : Float32) :: easings.map Prod.fst) hstrict i hltNext
      simpa [List.getElem!_eq_getElem?_getD, hgetK, hgetNext] using hadj

theorem piecewiseSegment_interior_nonzero_denom_Impl {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E) (t : Float32) (i : Nat)
    (hval : validateEasingKeyframes easing easings = some (keys, es))
    (hidx : floorBinarySearch keys t = (i : Int))
    (hposIdx : 0 < i) (hltNext : i + 1 < keys.length) :
    ∃ e pStart pEnd,
      piecewiseSegment keys es t = some (e, pStart, pEnd) ∧
      floatCompareLt pStart pEnd = true ∧
      floatKeyEq pStart pEnd = false := by
  rcases validateEasingKeyframes_strict_increasing_Impl easing easings keys es hval with
    ⟨rfl, rfl, hlenEq, _, hstrictTail, _⟩
  have hilt : i < ((0.0 : Float32) :: easings.map Prod.fst).length := by omega
  have hilt' : i < (easing :: easings.map Prod.snd).length := by
    simp only [List.length_cons, List.length_map] at hilt ⊢; exact hilt
  have hgetK : ((0.0 : Float32) :: easings.map Prod.fst)[i]? =
      some ((0.0 : Float32) :: easings.map Prod.fst)[i] := List.getElem?_eq_getElem hilt
  have hgetE : (easing :: easings.map Prod.snd)[i]? =
      some (easing :: easings.map Prod.snd)[i] := List.getElem?_eq_getElem hilt'
  have hgetNext : ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]? =
      some ((0.0 : Float32) :: easings.map Prod.fst)[i + 1] := List.getElem?_eq_getElem hltNext
  have hnonneg : ¬ ((i : Int) < 0) := by omega
  have hseg : piecewiseSegment ((0.0 : Float32) :: easings.map Prod.fst) (easing :: easings.map Prod.snd) t =
      some ((easing :: easings.map Prod.snd)[i], ((0.0 : Float32) :: easings.map Prod.fst)[i],
        ((0.0 : Float32) :: easings.map Prod.fst)[i + 1]) := by
    unfold piecewiseSegment
    rw [hidx]
    simp [hnonneg, hgetK, hgetE, hgetNext]
  refine ⟨(easing :: easings.map Prod.snd)[i], ((0.0 : Float32) :: easings.map Prod.fst)[i],
    ((0.0 : Float32) :: easings.map Prod.fst)[i + 1], hseg, ?_, ?_⟩
  · cases i with
    | zero => omega
    | succ j =>
      have hltTail : j + 1 < (easings.map Prod.fst).length := by simpa using hltNext
      have hadj := keysStrictlyIncreasing_adj (easings.map Prod.fst) hstrictTail j hltTail
      have hltj : j < (easings.map Prod.fst).length := by omega
      have hgetj : (easings.map Prod.fst)[j]? = some (easings.map Prod.fst)[j] := List.getElem?_eq_getElem hltj
      have hgetj1 : (easings.map Prod.fst)[j + 1]? = some (easings.map Prod.fst)[j + 1] :=
        List.getElem?_eq_getElem hltTail
      simp only [List.getElem!_eq_getElem?_getD, hgetj, hgetj1, Option.getD_some] at hadj
      simpa [List.getElem_cons_succ] using hadj
  · apply floatCompareLt_implies_not_floatKeyEq
    cases i with
    | zero => omega
    | succ j =>
      have hltTail : j + 1 < (easings.map Prod.fst).length := by simpa using hltNext
      have hadj := keysStrictlyIncreasing_adj (easings.map Prod.fst) hstrictTail j hltTail
      have hltj : j < (easings.map Prod.fst).length := by omega
      have hgetj : (easings.map Prod.fst)[j]? = some (easings.map Prod.fst)[j] := List.getElem?_eq_getElem hltj
      have hgetj1 : (easings.map Prod.fst)[j + 1]? = some (easings.map Prod.fst)[j + 1] :=
        List.getElem?_eq_getElem hltTail
      simp only [List.getElem!_eq_getElem?_getD, hgetj, hgetj1, Option.getD_some] at hadj
      simpa [List.getElem_cons_succ] using hadj

end UiCommon.Model

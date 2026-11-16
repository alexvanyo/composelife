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

import models.PeriodUntilModel

namespace TimeUtil.Model

/-! ### Bit-Vector & Two's-Complement Arithmetic Helpers -/

private theorem int32_bounds (x : Int32) :
    -(2 ^ 31 : Int) ≤ x.toInt ∧ x.toInt < (2 ^ 31 : Int) := by
  have h1 := x.toBitVec.le_toInt
  have h2 := x.toBitVec.toInt_lt
  change -(2 ^ (32 - 1) : Int) ≤ x.toInt at h1
  change x.toInt < (2 ^ (32 - 1) : Int) at h2
  omega

private theorem int64_bounds (x : Int64) :
    -(2 ^ 63 : Int) ≤ x.toInt ∧ x.toInt < (2 ^ 63 : Int) := by
  have h1 := x.toBitVec.le_toInt
  have h2 := x.toBitVec.toInt_lt
  change -(2 ^ (64 - 1) : Int) ≤ x.toInt at h1
  change x.toInt < (2 ^ (64 - 1) : Int) at h2
  omega

private theorem int64_ofInt_toInt {n : Int}
    (hlo : -(2 ^ 63 : Int) ≤ n) (hhi : n < (2 ^ 63 : Int)) :
    (Int64.ofInt n).toInt = n := by
  change (BitVec.ofInt 64 n).toInt = n
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le_mul_two] <;> omega

private theorem int64_add_toInt {a b : Int64}
    (hlo : -(2 ^ 63 : Int) ≤ a.toInt + b.toInt) (hhi : a.toInt + b.toInt < (2 ^ 63 : Int)) :
    (a + b).toInt = a.toInt + b.toInt := by
  change (a.toBitVec + b.toBitVec).toInt = a.toBitVec.toInt + b.toBitVec.toInt
  have hlo' : -(2 ^ 63 : Int) ≤ a.toBitVec.toInt + b.toBitVec.toInt := hlo
  have hhi' : a.toBitVec.toInt + b.toBitVec.toInt < (2 ^ 63 : Int) := hhi
  rw [BitVec.toInt_add, Int.bmod_eq_of_le_mul_two] <;> omega

private theorem int64_ofInt_eq_of_toInt {a : Int64} {n : Int}
    (h : a.toInt = n) : a = Int64.ofInt n := by
  apply Int64.toBitVec_inj.mp
  apply BitVec.eq_of_toInt_eq
  have hb := int64_bounds a
  rw [show (Int64.ofInt n).toBitVec.toInt = (Int64.ofInt n).toInt from rfl]
  rw [int64_ofInt_toInt (by omega) (by omega)]
  exact h

private theorem duration_ofNanos_isInNanos (x : Int64) :
    (Duration.ofNanos x).isInNanos = true := by
  dsimp only [Duration.isInNanos, Duration.ofNanos]
  have h0 : ((x.toUInt64 <<< 1) &&& 1) = 0 := by
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    change ((x.toUInt64.toBitVec <<< 1) &&& 1#64).toNat = 0
    rw [BitVec.toNat_and, BitVec.toNat_shiftLeft]
    have hx : (x.toUInt64.toBitVec.toNat * 2) % 2 ^ 64 % 2 = 0 := by omega
    simp [Nat.and_one_is_mod, Nat.shiftLeft_eq]
  rw [show ((x.toUInt64 <<< 1).toInt64.toUInt64) = (x.toUInt64 <<< 1) from rfl]
  rw [h0]
  rfl

private theorem duration_ofNanos_rawUnits {x : Int64}
    (hlo : -(2 ^ 62 : Int) ≤ x.toInt) (hhi : x.toInt < (2 ^ 62 : Int)) :
    (Duration.ofNanos x).rawUnits = x := by
  dsimp only [Duration.rawUnits, Duration.ofNanos]
  apply Int64.toBitVec_inj.mp
  apply BitVec.eq_of_toInt_eq
  have hb : (x.toUInt64 <<< 1).toInt64.toBitVec = x.toBitVec <<< 1 := rfl
  change (Int64.ofInt ((x.toUInt64 <<< 1).toInt64.toBitVec.sshiftRight 1).toInt).toInt = x.toInt
  rw [hb]
  have hbv : (x.toBitVec <<< 1).sshiftRight 1 = x.toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_sshiftRight]
    have hnotle : (!decide (64 ≤ i)) = true := by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
    rw [hnotle, Bool.true_and]
    by_cases hlt : 1 + i < 64
    · simp only [hlt, ↓reduceIte, BitVec.getLsbD_shiftLeft, decide_true, Bool.true_and]
      have h2 : (!decide (1 + i < 1)) = true := by
        simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
      rw [h2, Bool.true_and, Nat.add_sub_cancel_left]
    · have hi63 : i = 63 := by omega
      simp only [hlt, ↓reduceIte]
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
      simp only [show (64 - 1 : Nat) = 63 from rfl, show (!decide (63 < 1)) = true from rfl,
        show (63 - 1 : Nat) = 62 from rfl]
      have hmsb63 : x.toBitVec.getLsbD 63 = x.toBitVec.msb := by
        rw [BitVec.msb_eq_getLsbD_last]
      rw [hi63, hmsb63]
      cases hm : x.toBitVec.msb
      · have hlt262 : x.toBitVec.toNat < 2 ^ 62 := by
          have := BitVec.toInt_eq_toNat_cond x.toBitVec
          have hmsb_f : ¬ (2 ^ 63 ≤ x.toBitVec.toNat) := by
            rw [BitVec.msb_eq_toNat, decide_eq_false_iff_not] at hm; exact hm
          have hxint : x.toBitVec.toInt = ↑x.toBitVec.toNat := by
            rw [this, ite_eq_left (by omega)]
          have hhi' : x.toBitVec.toInt < 2 ^ 62 := hhi
          omega
        change x.toBitVec.toNat.testBit 62 = false
        have hdiv : (x.toBitVec.toNat / 2 ^ 62) % 2 = 0 := by
          rw [Nat.div_eq_of_lt hlt262]
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        rfl
      · have hge3262 : 3 * 2 ^ 62 ≤ x.toBitVec.toNat ∧ x.toBitVec.toNat < 2 ^ 64 := by
          have := BitVec.toInt_eq_toNat_cond x.toBitVec
          have hmsb_t : 2 ^ 63 ≤ x.toBitVec.toNat := by
            rw [BitVec.msb_eq_toNat, decide_eq_true_eq] at hm; exact hm
          have hlt64 : x.toBitVec.toNat < 2 ^ 64 := x.toBitVec.isLt
          have hxint : x.toBitVec.toInt = ↑x.toBitVec.toNat - 2 ^ 64 := by
            rw [this, ite_eq_right (by omega)]; rfl
          have hlo' : -(2 ^ 62 : Int) ≤ x.toBitVec.toInt := hlo
          omega
        change x.toBitVec.toNat.testBit 62 = true
        have hdiv : (x.toBitVec.toNat / 2 ^ 62) % 2 = 1 := by
          have hd : x.toBitVec.toNat / 2 ^ 62 = 3 := by omega
          rw [hd]
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
        rfl
  rw [hbv]
  change (Int64.ofInt x.toInt).toInt = x.toInt
  exact int64_ofInt_toInt (by omega) (by omega)

private theorem duration_ofNanos_inWholeNanoseconds {x : Int64}
    (hlo : -(4611686018426999999 : Int) ≤ x.toInt) (hhi : x.toInt ≤ 4611686018426999999) :
    (Duration.ofNanos x).inWholeNanoseconds = x := by
  dsimp only [Duration.inWholeNanoseconds]
  rw [duration_ofNanos_isInNanos]
  exact duration_ofNanos_rawUnits (by omega) (by omega)

private theorem duration_ofNanos_plus_zero {x : Int64}
    (hlo : -(4611686018426999999 : Int) ≤ x.toInt) (hhi : x.toInt ≤ 4611686018426999999) :
    Duration.plus (Duration.ofNanos x) Duration.zero = Duration.ofNanos x := by
  have hz_in : Duration.zero.isInNanos = true := rfl
  have hz_raw : Duration.zero.rawUnits = 0 := rfl
  have hx_in : (Duration.ofNanos x).isInNanos = true := duration_ofNanos_isInNanos x
  have hx_raw : (Duration.ofNanos x).rawUnits = x := duration_ofNanos_rawUnits (by omega) (by omega)
  dsimp only [Duration.plus, Duration.plus?]
  rw [hx_in, hz_in, hx_raw, hz_raw]
  simp [Duration.ofNanosNormalized, hlo, hhi]

/-! ### `totalNanosecondsModel` Exactness and Additivity -/

theorem totalNanosecondsModel_exact_bounded_Impl (p : DateTimePeriodModel)
    (hm : -(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433)
    (hh : -(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023)
    (hsum :
      -(2 ^ 63 : Int) ≤
        p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) ∧
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) <
        (2 ^ 63 : Int)) :
    (totalNanosecondsModel p).toInt =
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) := by
  have hns_b := int32_bounds p.nanoseconds
  have hs_b := int32_bounds p.seconds
  have hns_i : (Int64.ofInt p.nanoseconds.toInt).toInt = p.nanoseconds.toInt :=
    int64_ofInt_toInt (by omega) (by omega)
  have hs_dur : Duration.ofIntUnit p.seconds .seconds =
      Duration.ofNanos (Int64.ofInt (p.seconds.toInt * 1000000000)) := by
    dsimp only [Duration.ofIntUnit, Duration.ofLongUnit]
    have hsi : (Int64.ofInt p.seconds.toInt).toInt = p.seconds.toInt :=
      int64_ofInt_toInt (by omega) (by omega)
    rw [hsi]
    simp only [show (-(4611686018 : Int) ≤ p.seconds.toInt ∧ p.seconds.toInt ≤ 4611686018) from by omega,
      and_self, ↓reduceIte]
  have hs_ns : (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds =
      Int64.ofInt (p.seconds.toInt * 1000000000) := by
    rw [hs_dur]
    apply duration_ofNanos_inWholeNanoseconds <;>
      rw [int64_ofInt_toInt (by omega) (by omega)] <;> omega
  have hs_val : (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds.toInt =
      p.seconds.toInt * 1000000000 := by
    rw [hs_ns]
    exact int64_ofInt_toInt (by omega) (by omega)
  have hm_dur : Duration.ofIntUnit p.minutes .minutes =
      Duration.ofNanos (Int64.ofInt (p.minutes.toInt * 60000000000)) := by
    dsimp only [Duration.ofIntUnit, Duration.ofLongUnit]
    have hmi : (Int64.ofInt p.minutes.toInt).toInt = p.minutes.toInt :=
      int64_ofInt_toInt (by omega) (by omega)
    rw [hmi]
    simp only [hm, and_self, ↓reduceIte]
  have hm_ns : (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds =
      Int64.ofInt (p.minutes.toInt * 60000000000) := by
    rw [hm_dur]
    apply duration_ofNanos_inWholeNanoseconds <;>
      rw [int64_ofInt_toInt (by omega) (by omega)] <;> omega
  have hm_val : (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds.toInt =
      p.minutes.toInt * 60000000000 := by
    rw [hm_ns]
    exact int64_ofInt_toInt (by omega) (by omega)
  have hh_dur : Duration.ofIntUnit p.hours .hours =
      Duration.ofNanos (Int64.ofInt (p.hours.toInt * 3600000000000)) := by
    dsimp only [Duration.ofIntUnit, Duration.ofLongUnit]
    have hhi : (Int64.ofInt p.hours.toInt).toInt = p.hours.toInt :=
      int64_ofInt_toInt (by omega) (by omega)
    rw [hhi]
    simp only [hh, and_self, ↓reduceIte]
  have hh_ns : (Duration.ofIntUnit p.hours .hours).inWholeNanoseconds =
      Int64.ofInt (p.hours.toInt * 3600000000000) := by
    rw [hh_dur]
    apply duration_ofNanos_inWholeNanoseconds <;>
      rw [int64_ofInt_toInt (by omega) (by omega)] <;> omega
  have hh_val : (Duration.ofIntUnit p.hours .hours).inWholeNanoseconds.toInt =
      p.hours.toInt * 3600000000000 := by
    rw [hh_ns]
    exact int64_ofInt_toInt (by omega) (by omega)
  dsimp only [totalNanosecondsModel]
  have h1 : (Int64.ofInt p.nanoseconds.toInt + (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds).toInt =
      p.nanoseconds.toInt + p.seconds.toInt * 1000000000 := by
    rw [int64_add_toInt (by omega) (by omega), hns_i, hs_val]
  have h2 : (Int64.ofInt p.nanoseconds.toInt + (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds +
      (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds).toInt =
      p.nanoseconds.toInt + p.seconds.toInt * 1000000000 + p.minutes.toInt * 60000000000 := by
    rw [int64_add_toInt (by omega) (by omega), h1, hm_val]
  rw [int64_add_toInt (by omega) (by omega), h2, hh_val]
  omega

theorem totalNanosecondsModel_additive_Impl (p q sum : DateTimePeriodModel)
    (hns : sum.nanoseconds.toInt = p.nanoseconds.toInt + q.nanoseconds.toInt)
    (hs : sum.seconds.toInt = p.seconds.toInt + q.seconds.toInt)
    (hm : sum.minutes.toInt = p.minutes.toInt + q.minutes.toInt)
    (hh : sum.hours.toInt = p.hours.toInt + q.hours.toInt)
    (hmp : -(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433)
    (hhp : -(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023)
    (hsump :
      -(2 ^ 63 : Int) ≤
        p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) ∧
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) <
        (2 ^ 63 : Int))
    (hmq : -(76861433 : Int) ≤ q.minutes.toInt ∧ q.minutes.toInt ≤ 76861433)
    (hhq : -(1281023 : Int) ≤ q.hours.toInt ∧ q.hours.toInt ≤ 1281023)
    (hsumq :
      -(2 ^ 63 : Int) ≤
        q.nanoseconds.toInt + 1000000000 * (q.seconds.toInt + 60 * q.minutes.toInt + 3600 * q.hours.toInt) ∧
      q.nanoseconds.toInt + 1000000000 * (q.seconds.toInt + 60 * q.minutes.toInt + 3600 * q.hours.toInt) <
        (2 ^ 63 : Int))
    (hmsum : -(76861433 : Int) ≤ sum.minutes.toInt ∧ sum.minutes.toInt ≤ 76861433)
    (hhsum : -(1281023 : Int) ≤ sum.hours.toInt ∧ sum.hours.toInt ≤ 1281023)
    (hsumsum :
      -(2 ^ 63 : Int) ≤
        sum.nanoseconds.toInt +
          1000000000 * (sum.seconds.toInt + 60 * sum.minutes.toInt + 3600 * sum.hours.toInt) ∧
      sum.nanoseconds.toInt +
          1000000000 * (sum.seconds.toInt + 60 * sum.minutes.toInt + 3600 * sum.hours.toInt) <
        (2 ^ 63 : Int)) :
    (totalNanosecondsModel sum).toInt =
      (totalNanosecondsModel p).toInt + (totalNanosecondsModel q).toInt := by
  rw [totalNanosecondsModel_exact_bounded_Impl p hmp hhp hsump]
  rw [totalNanosecondsModel_exact_bounded_Impl q hmq hhq hsumq]
  rw [totalNanosecondsModel_exact_bounded_Impl sum hmsum hhsum hsumsum]
  rw [hns, hs, hm, hh]
  omega

/-! ### Euclidean Truncation Toward Zero for `dateComponentInWholeUnits` and `timeComponentInWholeUnits` -/

private theorem int_tdiv_add_tmod (a b : Int) :
    (a.tdiv b) * b + a.tmod b = a := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      change (↑(m / n) : Int) * ↑n + ↑(m % n) = ↑m
      rw [← Int.natCast_mul, ← Int.natCast_add, Nat.mul_comm, Nat.div_add_mod]
    | negSucc n =>
      change -(↑(m / (n + 1)) : Int) * Int.negSucc n + ↑(m % (n + 1)) = ↑m
      rw [Int.negSucc_eq, Int.neg_mul_neg, ← Int.natCast_succ n, ← Int.natCast_mul,
        ← Int.natCast_add, Nat.mul_comm, Nat.div_add_mod]
  | negSucc m =>
    cases b with
    | ofNat n =>
      change -(↑((m + 1) / n) : Int) * ↑n + -(↑((m + 1) % n) : Int) = Int.negSucc m
      rw [Int.neg_mul, ← Int.natCast_mul, Int.negSucc_eq]
      have h := Nat.div_add_mod (m + 1) n
      rw [Nat.mul_comm] at h
      omega
    | negSucc n =>
      change (↑((m + 1) / (n + 1)) : Int) * Int.negSucc n + -(↑((m + 1) % (n + 1)) : Int) = Int.negSucc m
      rw [Int.negSucc_eq, Int.mul_neg, ← Int.natCast_succ n, ← Int.natCast_mul, Int.negSucc_eq]
      have h := Nat.div_add_mod (m + 1) (n + 1)
      rw [Nat.mul_comm] at h
      rw [Nat.succ_eq_add_one]
      omega

private theorem int_tdiv_nonpos_of_nonpos {a b : Int} (ha : a ≤ 0) (hb : 0 ≤ b) :
    a.tdiv b ≤ 0 := by
  cases a with
  | ofNat m =>
    cases m with
    | zero =>
      cases b with
      | ofNat n => simp [Int.tdiv]
      | negSucc n => cases hb
    | succ k => cases ha
  | negSucc m =>
    cases b with
    | ofNat n =>
      change -(↑((m + 1) / n) : Int) ≤ 0
      have h0 : (0 : Int) ≤ ↑((m + 1) / n) := Int.natCast_nonneg _
      omega
    | negSucc n => cases hb

private theorem int_tmod_nonneg_of_nonneg {a b : Int} (ha : 0 ≤ a) :
    0 ≤ a.tmod b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => change (0 : Int) ≤ ↑(m % n); exact Int.natCast_nonneg _
    | negSucc n => change (0 : Int) ≤ ↑(m % (n + 1)); exact Int.natCast_nonneg _
  | negSucc m => cases ha

private theorem int_tmod_nonpos_of_nonpos {a b : Int} (ha : a ≤ 0) :
    a.tmod b ≤ 0 := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => cases b <;> simp [Int.tmod]
    | succ k => cases ha
  | negSucc m =>
    cases b with
    | ofNat n =>
      change -(↑((m + 1) % n) : Int) ≤ 0
      have h0 : (0 : Int) ≤ ↑((m + 1) % n) := Int.natCast_nonneg _
      omega
    | negSucc n =>
      change -(↑((m + 1) % (n + 1)) : Int) ≤ 0
      have h0 : (0 : Int) ≤ ↑((m + 1) % (n + 1)) := Int.natCast_nonneg _
      omega

private theorem int_tmod_natAbs_lt {a b : Int} (hb : 0 < b) :
    (a.tmod b).natAbs < b.natAbs := by
  cases b with
  | ofNat n =>
    have hn : 0 < n := Int.ofNat_lt.mp hb
    cases a with
    | ofNat m =>
      change (Int.ofNat (m % n)).natAbs < (Int.ofNat n).natAbs
      exact Nat.mod_lt m hn
    | negSucc m =>
      change (-Int.ofNat ((m + 1) % n)).natAbs < (Int.ofNat n).natAbs
      simp only [Int.natAbs_neg]
      exact Nat.mod_lt (m + 1) hn
  | negSucc n => cases hb

private theorem int32_sdiv_toInt_of_pos (a b : Int32) (hb : 0 < b.toInt) :
    (jvmI32Div a b).toInt = a.toInt.tdiv b.toInt := by
  have ha := int32_bounds a
  have hbb := int32_bounds b
  have hq : -(2 ^ 31 : Int) ≤ a.toInt.tdiv b.toInt ∧ a.toInt.tdiv b.toInt < (2 ^ 31 : Int) := by
    cases ha_eq : a.toInt with
    | ofNat m =>
      rw [ha_eq] at ha
      cases hb_eq : b.toInt with
      | ofNat n =>
        change -(2 ^ 31 : Int) ≤ ↑(m / n) ∧ (↑(m / n) : Int) < (2 ^ 31 : Int)
        have hm_lt : (m : Int) < 2 ^ 31 := ha.2
        have hdiv : (↑(m / n) : Int) ≤ (m : Int) := Int.ofNat_le.mpr (Nat.div_le_self m n)
        have h0 : (0 : Int) ≤ ↑(m / n) := Int.natCast_nonneg _
        omega
      | negSucc n => rw [hb_eq] at hb; cases hb
    | negSucc m =>
      rw [ha_eq] at ha
      cases hb_eq : b.toInt with
      | ofNat n =>
        change -(2 ^ 31 : Int) ≤ -(↑((m + 1) / n) : Int) ∧ -(↑((m + 1) / n) : Int) < (2 ^ 31 : Int)
        have hm_ge : -(2 ^ 31 : Int) ≤ -((m + 1 : Nat) : Int) := by
          have := ha.1; rw [Int.negSucc_eq] at this; exact this
        have hdiv : (↑((m + 1) / n) : Int) ≤ ↑(m + 1) := Int.ofNat_le.mpr (Nat.div_le_self (m + 1) n)
        have h0 : (0 : Int) ≤ ↑((m + 1) / n) := Int.natCast_nonneg _
        omega
      | negSucc n => rw [hb_eq] at hb; cases hb
  dsimp only [jvmI32Div]
  change (BitVec.ofInt 32 (BitVec.sdiv a.toBitVec b.toBitVec).toInt).toInt = a.toInt.tdiv b.toInt
  rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]
  have hmod1 : (a.toBitVec.toInt.tdiv b.toBitVec.toInt).bmod (2 ^ 32) = a.toInt.tdiv b.toInt := by
    change (a.toInt.tdiv b.toInt).bmod (2 ^ 32) = a.toInt.tdiv b.toInt
    rw [Int.bmod_eq_of_le_mul_two] <;> omega
  rw [hmod1, Int.bmod_eq_of_le_mul_two] <;> omega

private theorem int64_sdiv_toInt_of_pos (a b : Int64) (hb : 0 < b.toInt) :
    (jvmI64Div a b).toInt = a.toInt.tdiv b.toInt := by
  have ha := int64_bounds a
  have hbb := int64_bounds b
  have hq : -(2 ^ 63 : Int) ≤ a.toInt.tdiv b.toInt ∧ a.toInt.tdiv b.toInt < (2 ^ 63 : Int) := by
    cases ha_eq : a.toInt with
    | ofNat m =>
      rw [ha_eq] at ha
      cases hb_eq : b.toInt with
      | ofNat n =>
        change -(2 ^ 63 : Int) ≤ ↑(m / n) ∧ (↑(m / n) : Int) < (2 ^ 63 : Int)
        have hm_lt : (m : Int) < 2 ^ 63 := ha.2
        have hdiv : (↑(m / n) : Int) ≤ (m : Int) := Int.ofNat_le.mpr (Nat.div_le_self m n)
        have h0 : (0 : Int) ≤ ↑(m / n) := Int.natCast_nonneg _
        omega
      | negSucc n => rw [hb_eq] at hb; cases hb
    | negSucc m =>
      rw [ha_eq] at ha
      cases hb_eq : b.toInt with
      | ofNat n =>
        change -(2 ^ 63 : Int) ≤ -(↑((m + 1) / n) : Int) ∧ -(↑((m + 1) / n) : Int) < (2 ^ 63 : Int)
        have hm_ge : -(2 ^ 63 : Int) ≤ -((m + 1 : Nat) : Int) := by
          have := ha.1; rw [Int.negSucc_eq] at this; exact this
        have hdiv : (↑((m + 1) / n) : Int) ≤ ↑(m + 1) := Int.ofNat_le.mpr (Nat.div_le_self (m + 1) n)
        have h0 : (0 : Int) ≤ ↑((m + 1) / n) := Int.natCast_nonneg _
        omega
      | negSucc n => rw [hb_eq] at hb; cases hb
  dsimp only [jvmI64Div]
  change (BitVec.ofInt 64 (BitVec.sdiv a.toBitVec b.toBitVec).toInt).toInt = a.toInt.tdiv b.toInt
  rw [BitVec.toInt_ofInt, BitVec.toInt_sdiv]
  have hmod1 : (a.toBitVec.toInt.tdiv b.toBitVec.toInt).bmod (2 ^ 64) = a.toInt.tdiv b.toInt := by
    change (a.toInt.tdiv b.toInt).bmod (2 ^ 64) = a.toInt.tdiv b.toInt
    rw [Int.bmod_eq_of_le_mul_two] <;> omega
  rw [hmod1, Int.bmod_eq_of_le_mul_two] <;> omega

theorem dateComponentInWholeUnitsModel_trap_zero_Impl (p : DateTimePeriodModel) :
    dateComponentInWholeUnitsModel p (.dayBased 0) = none ∧
    dateComponentInWholeUnitsModel p (.monthBased 0) = none :=
  ⟨rfl, rfl⟩

theorem dateComponentInWholeUnitsModel_dayBased_truncation_Impl
    (p : DateTimePeriodModel) (d : Int32) (hd : 0 < d.toInt) :
    ∃ q, dateComponentInWholeUnitsModel p (.dayBased d) = some q ∧
      let r := p.days.toInt - q.toInt * d.toInt
      q.toInt * d.toInt + r = p.days.toInt ∧
      r.natAbs < d.toInt.natAbs ∧
      (0 ≤ p.days.toInt → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (p.days.toInt ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (p.days = 0 → q = 0) := by
  have hd0 : (d == 0) = false := beq_false_of_ne (fun h => by
    have hz : (0 : Int32).toInt = 0 := rfl
    rw [h, hz] at hd; omega)
  refine ⟨jvmI32Div p.days d, ?_, ?_⟩
  · simp [dateComponentInWholeUnitsModel, hd0]
  · have hq : (jvmI32Div p.days d).toInt = p.days.toInt.tdiv d.toInt :=
      int32_sdiv_toInt_of_pos p.days d hd
    have hrem : p.days.toInt - (jvmI32Div p.days d).toInt * d.toInt = p.days.toInt.tmod d.toInt := by
      have hadd := int_tdiv_add_tmod p.days.toInt d.toInt
      rw [hq]
      omega
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [hrem]
      exact int_tmod_natAbs_lt hd
    · intro hnn
      rw [hrem, hq]
      exact ⟨Int.tdiv_nonneg hnn (by omega), int_tmod_nonneg_of_nonneg hnn⟩
    · intro hnp
      rw [hrem, hq]
      exact ⟨int_tdiv_nonpos_of_nonpos hnp (by omega), int_tmod_nonpos_of_nonpos hnp⟩
    · intro hz
      apply Int32.toBitVec_inj.mp
      apply BitVec.eq_of_toInt_eq
      change (jvmI32Div p.days d).toInt = (0 : Int32).toInt
      rw [hq, hz]
      simp

theorem dateComponentInWholeUnitsModel_monthBased_truncation_Impl
    (p : DateTimePeriodModel) (m : Int32) (hm : 0 < m.toInt) :
    ∃ q, dateComponentInWholeUnitsModel p (.monthBased m) = some q ∧
      let r := p.months.toInt - q.toInt * m.toInt
      q.toInt * m.toInt + r = p.months.toInt ∧
      r.natAbs < m.toInt.natAbs ∧
      (0 ≤ p.months.toInt → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (p.months.toInt ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (p.months = 0 → q = 0) := by
  have hm0 : (m == 0) = false := beq_false_of_ne (fun h => by
    have hz : (0 : Int32).toInt = 0 := rfl
    rw [h, hz] at hm; omega)
  refine ⟨jvmI32Div p.months m, ?_, ?_⟩
  · simp [dateComponentInWholeUnitsModel, hm0]
  · have hq : (jvmI32Div p.months m).toInt = p.months.toInt.tdiv m.toInt :=
      int32_sdiv_toInt_of_pos p.months m hm
    have hrem : p.months.toInt - (jvmI32Div p.months m).toInt * m.toInt =
        p.months.toInt.tmod m.toInt := by
      have hadd := int_tdiv_add_tmod p.months.toInt m.toInt
      rw [hq]
      omega
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [hrem]
      exact int_tmod_natAbs_lt hm
    · intro hnn
      rw [hrem, hq]
      exact ⟨Int.tdiv_nonneg hnn (by omega), int_tmod_nonneg_of_nonneg hnn⟩
    · intro hnp
      rw [hrem, hq]
      exact ⟨int_tdiv_nonpos_of_nonpos hnp (by omega), int_tmod_nonpos_of_nonpos hnp⟩
    · intro hz
      apply Int32.toBitVec_inj.mp
      apply BitVec.eq_of_toInt_eq
      change (jvmI32Div p.months m).toInt = (0 : Int32).toInt
      rw [hq, hz]
      simp

theorem timeComponentInWholeUnitsModel_trap_zero_Impl (p : DateTimePeriodModel) :
    timeComponentInWholeUnitsModel p ⟨0⟩ = none := rfl

theorem timeComponentInWholeUnitsModel_truncation_Impl
    (p : DateTimePeriodModel) (u : TimeBasedUnit) (hu : 0 < u.nanoseconds.toInt) :
    ∃ q, timeComponentInWholeUnitsModel p u = some q ∧
      let total := (totalNanosecondsModel p).toInt
      let r := total - q.toInt * u.nanoseconds.toInt
      q.toInt * u.nanoseconds.toInt + r = total ∧
      r.natAbs < u.nanoseconds.toInt.natAbs ∧
      (0 ≤ total → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (total ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (totalNanosecondsModel p = 0 → q = 0) := by
  have hu0 : (u.nanoseconds == 0) = false := beq_false_of_ne (fun h => by
    have hz : (0 : Int64).toInt = 0 := rfl
    rw [h, hz] at hu; omega)
  refine ⟨jvmI64Div (totalNanosecondsModel p) u.nanoseconds, ?_, ?_⟩
  · simp [timeComponentInWholeUnitsModel, hu0]
  · have hq : (jvmI64Div (totalNanosecondsModel p) u.nanoseconds).toInt =
        (totalNanosecondsModel p).toInt.tdiv u.nanoseconds.toInt :=
      int64_sdiv_toInt_of_pos (totalNanosecondsModel p) u.nanoseconds hu
    have hrem : (totalNanosecondsModel p).toInt -
          (jvmI64Div (totalNanosecondsModel p) u.nanoseconds).toInt * u.nanoseconds.toInt =
        (totalNanosecondsModel p).toInt.tmod u.nanoseconds.toInt := by
      have hadd := int_tdiv_add_tmod (totalNanosecondsModel p).toInt u.nanoseconds.toInt
      rw [hq]
      omega
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · rw [hrem]
      exact int_tmod_natAbs_lt hu
    · intro hnn
      rw [hrem, hq]
      exact ⟨Int.tdiv_nonneg hnn (by omega), int_tmod_nonneg_of_nonneg hnn⟩
    · intro hnp
      rw [hrem, hq]
      exact ⟨int_tdiv_nonpos_of_nonpos hnp (by omega), int_tmod_nonpos_of_nonpos hnp⟩
    · intro hz
      apply Int64.toBitVec_inj.mp
      apply BitVec.eq_of_toInt_eq
      change (jvmI64Div (totalNanosecondsModel p) u.nanoseconds).toInt = (0 : Int64).toInt
      rw [hq, hz]
      simp

/-! ### `Duration` & Approximate Duration Formula Consistency and Bounds -/

theorem timeComponentDurationModel_nanoseconds_exact_Impl (p : DateTimePeriodModel)
    (hb : (-4611686018426999999 : Int) ≤ (totalNanosecondsModel p).toInt ∧
      (totalNanosecondsModel p).toInt ≤ 4611686018426999999) :
    (timeComponentDurationModel p).inWholeNanoseconds = totalNanosecondsModel p := by
  dsimp only [timeComponentDurationModel, Duration.ofLongUnit, Duration.ofNanosNormalized]
  simp only [hb, and_self, ↓reduceIte]
  exact duration_ofNanos_inWholeNanoseconds hb.1 hb.2

theorem dateComponentApproximateDurationModel_formula_Impl (p : DateTimePeriodModel) :
    dateComponentApproximateDurationModel p =
      Duration.ofLongUnit
        (Duration.plus (Duration.ofIntUnit p.days .days)
          (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).inWholeNanoseconds
        .nanoseconds := rfl

theorem dateComponentApproximateDurationModel_days_only_Impl (p : DateTimePeriodModel)
    (hy : p.years = 0) (hm : p.months = 0)
    (hd : (-53375 : Int) ≤ p.days.toInt ∧ p.days.toInt ≤ 53375) :
    (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt =
      p.days.toInt * 86400000000000 := by
  have hzeroF : Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422) =
      Duration.zero := by
    rw [hy, hm]
    rfl
  have hdayI : (Int64.ofInt p.days.toInt).toInt = p.days.toInt :=
    int64_ofInt_toInt (by omega) (by omega)
  have hdayDur : Duration.ofIntUnit p.days .days =
      Duration.ofNanos (Int64.ofInt (p.days.toInt * 86400000000000)) := by
    dsimp only [Duration.ofIntUnit, Duration.ofLongUnit]
    rw [hdayI]
    simp only [hd, and_self, ↓reduceIte]
  have hdayNs : (Int64.ofInt (p.days.toInt * 86400000000000)).toInt =
      p.days.toInt * 86400000000000 :=
    int64_ofInt_toInt (by omega) (by omega)
  dsimp only [dateComponentApproximateDurationModel]
  rw [hzeroF, hdayDur]
  rw [duration_ofNanos_plus_zero (by rw [hdayNs]; omega) (by rw [hdayNs]; omega)]
  rw [duration_ofNanos_inWholeNanoseconds (by rw [hdayNs]; omega) (by rw [hdayNs]; omega)]
  dsimp only [Duration.ofLongUnit, Duration.ofNanosNormalized]
  simp only [show (-4611686018426999999 : Int) ≤ (Int64.ofInt (p.days.toInt * 86400000000000)).toInt ∧
      (Int64.ofInt (p.days.toInt * 86400000000000)).toInt ≤ 4611686018426999999 from by
    rw [hdayNs]; omega, and_self, ↓reduceIte]
  rw [duration_ofNanos_inWholeNanoseconds (by rw [hdayNs]; omega) (by rw [hdayNs]; omega)]
  exact hdayNs

theorem approximateDurationInMinutesModel_formula_Impl (p : DateTimePeriodModel) :
    approximateDurationInMinutesModel p =
      Jvm.i64ToFloat (approximateDurationModel p).inWholeNanoseconds.toUInt64 / 60000000000.0 := rfl

theorem approximateDurationInMinutesModel_zero_Impl :
    approximateDurationInMinutesModel {} = 0.0 := by
  have h1 : timeComponentDurationModel {} = Duration.zero := rfl
  have h2 : dateComponentApproximateDurationModel {} = Duration.zero := by
    dsimp only [dateComponentApproximateDurationModel]
    have hf : Duration.ofDaysFloat (((0 : Int32).toFloat / 12.0 + (0 : Int32).toFloat) * 365.2422) =
        Duration.zero := rfl
    have hd : Duration.ofIntUnit 0 .days = Duration.zero := rfl
    rw [hf, hd]
    rfl
  dsimp only [approximateDurationInMinutesModel, approximateDurationModel]
  rw [h1, h2]
  rfl

theorem approximateDurationInMinutesModel_ninety_minutes_Impl :
    (approximateDurationInMinutesModel { hours := 1, minutes := 30 }).toBits = (90.0 : Float).toBits ∧
    (approximateDurationInMinutesModel { hours := 1, minutes := 30 } == 90.0) = true := by
  have ht : totalNanosecondsModel { hours := 1, minutes := 30 } = 5400000000000 := by
    dsimp only [totalNanosecondsModel]
    have h1 : Duration.ofIntUnit 0 .seconds = Duration.zero := rfl
    have h2 : Duration.ofIntUnit 30 .minutes = Duration.ofNanos 1800000000000 := by decide +kernel
    have h3 : Duration.ofIntUnit 1 .hours = Duration.ofNanos 3600000000000 := by decide +kernel
    rw [h1, h2, h3]
    decide +kernel
  have htc : timeComponentDurationModel { hours := 1, minutes := 30 } =
      Duration.ofNanos 5400000000000 := by
    dsimp only [timeComponentDurationModel]
    rw [ht]
    decide +kernel
  have hdc : dateComponentApproximateDurationModel { hours := 1, minutes := 30 } = Duration.zero := by
    dsimp only [dateComponentApproximateDurationModel]
    have hf : Duration.ofDaysFloat (((0 : Int32).toFloat / 12.0 + (0 : Int32).toFloat) * 365.2422) =
        Duration.zero := rfl
    have hd : Duration.ofIntUnit 0 .days = Duration.zero := rfl
    rw [hf, hd]
    rfl
  have hns : (approximateDurationModel { hours := 1, minutes := 30 }).inWholeNanoseconds =
      5400000000000 := by
    dsimp only [approximateDurationModel]
    rw [htc, hdc]
    rw [duration_ofNanos_plus_zero (by decide) (by decide)]
    exact duration_ofNanos_inWholeNanoseconds (by decide) (by decide)
  have h1m : (Duration.ofIntUnit 1 .minutes).inWholeNanoseconds = 60000000000 := by decide +kernel
  have hu1 : (5400000000000 : Int64).toUInt64 = 5400000000000 := rfl
  have hu2 : (60000000000 : Int64).toUInt64 = 60000000000 := rfl
  have hf1 : Jvm.i64ToFloat (5400000000000 : UInt64) = 5400000000000.0 := by
    have hs : (5400000000000 : UInt64).toBitVec.slt 0#64 = false := by decide +kernel
    dsimp only [Jvm.i64ToFloat]
    rw [hs]
    rfl
  have hf2 : Jvm.i64ToFloat (60000000000 : UInt64) = 60000000000.0 := by
    have hs : (60000000000 : UInt64).toBitVec.slt 0#64 = false := by decide +kernel
    dsimp only [Jvm.i64ToFloat]
    rw [hs]
    rfl
  dsimp only [approximateDurationInMinutesModel]
  rw [hns, h1m]
  change (Jvm.i64ToFloat (5400000000000 : Int64).toUInt64 /
      Jvm.i64ToFloat (60000000000 : Int64).toUInt64).toBits = (90.0 : Float).toBits ∧
    ((Jvm.i64ToFloat (5400000000000 : Int64).toUInt64 /
      Jvm.i64ToFloat (60000000000 : Int64).toUInt64) == 90.0) = true
  rw [hu1, hu2, hf1, hf2]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem dateComponentApproximateDurationModel_inWholeNanoseconds_bounded_Impl
    (p : DateTimePeriodModel) :
    -(2 ^ 63 : Int) ≤ (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt ∧
    (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt < (2 ^ 63 : Int) :=
  int64_bounds (dateComponentApproximateDurationModel p).inWholeNanoseconds

theorem approximateDurationModel_inWholeNanoseconds_bounded_Impl
    (p : DateTimePeriodModel) :
    -(2 ^ 63 : Int) ≤ (approximateDurationModel p).inWholeNanoseconds.toInt ∧
    (approximateDurationModel p).inWholeNanoseconds.toInt < (2 ^ 63 : Int) :=
  int64_bounds (approximateDurationModel p).inWholeNanoseconds

end TimeUtil.Model

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

import models.CalculatorModel

namespace MosaicCalculator.Model

theorem reduceCalculatorState_clear_resets_Impl (st : CalculatorState) :
    reduceCalculatorStateModel st .clear = CalculatorState.initial := rfl

theorem reduceCalculatorState_divZero_enters_error_Impl (lhs : Int64) :
    reduceCalculatorStateModel
      { displayValue := 0, pendingOperand := some lhs, pendingOp := some .div, enteringNewNumber := false, error := none }
      .equals = { error := some .divideByZero } := by
  dsimp [reduceCalculatorStateModel, applyOpModel, checkedDivModel, Option.isSome]

private theorem u64_slt_zero_of_msb_false {x : UInt64} (h : x.toBitVec.msb = false) :
    x.toBitVec.slt 0#64 = false := by
  rw [BitVec.msb_eq_toNat, decide_eq_false_iff_not] at h
  change decide (x.toBitVec.toInt < (0#64 : BitVec 64).toInt) = false
  rw [decide_eq_false_iff_not, BitVec.toInt_eq_toNat_cond]
  have h0 : (0#64 : BitVec 64).toInt = 0 := rfl
  have hlt : 2 * x.toBitVec.toNat < 2 ^ 64 := by
    change 2 * x.toNat < 2 ^ 64
    change ¬ (2 ^ 63 ≤ x.toNat) at h
    omega
  simp only [hlt, ↓reduceIte, h0]
  omega

private theorem u64_msb_false_of_lt {x : UInt64} (h : x.toNat < 2 ^ 63) :
    x.toBitVec.msb = false := by
  rw [BitVec.msb_eq_toNat]
  exact decide_eq_false (by change ¬ (2 ^ 63 ≤ x.toNat); omega)

theorem checkedAddModel_nonneg_small_Impl (a b : Int64)
    (ha : 0 ≤ a.toInt ∧ a.toInt ≤ 1000000) (hb : 0 ≤ b.toInt ∧ b.toInt ≤ 1000000) :
    checkedAddModel a b = .value (Int64.ofInt (a.toInt + b.toInt)) := by
  have ha_nat : a.toUInt64.toNat = a.toInt.toNat := by
    change a.toBitVec.toNat = a.toBitVec.toInt.toNat
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · omega
    · next hge =>
      have hnonneg : 0 ≤ a.toInt := ha.1
      change 0 ≤ a.toBitVec.toInt at hnonneg
      rw [BitVec.toInt_eq_toNat_cond] at hnonneg
      simp [hge] at hnonneg
      omega
  have hb_nat : b.toUInt64.toNat = b.toInt.toNat := by
    change b.toBitVec.toNat = b.toBitVec.toInt.toNat
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · omega
    · next hge =>
      have hnonneg : 0 ≤ b.toInt := hb.1
      change 0 ≤ b.toBitVec.toInt at hnonneg
      rw [BitVec.toInt_eq_toNat_cond] at hnonneg
      simp [hge] at hnonneg
      omega
  have hsum_nat : (a.toUInt64 + b.toUInt64).toNat = a.toUInt64.toNat + b.toUInt64.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have ha_msb : a.toUInt64.toBitVec.msb = false := u64_msb_false_of_lt (by omega)
  have hres_msb : (a.toUInt64 + b.toUInt64).toBitVec.msb = false := u64_msb_false_of_lt (by omega)
  have hchk : (((a.toUInt64 ^^^ (a.toUInt64 + b.toUInt64)) &&&
      (b.toUInt64 ^^^ (a.toUInt64 + b.toUInt64))).toBitVec.slt 0#64) = false := by
    apply u64_slt_zero_of_msb_false
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.msb_and, BitVec.msb_xor,
      ha_msb, hres_msb, Bool.bne_false, Bool.false_and]
  dsimp [checkedAddModel]
  rw [hchk]
  simp only [Bool.false_eq_true, ↓reduceIte, CheckedEvalResult.value.injEq]
  apply Int64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  change (a.toUInt64 + b.toUInt64).toBitVec.toNat = (BitVec.ofInt 64 (a.toInt + b.toInt)).toNat
  have hlhs : (a.toUInt64 + b.toUInt64).toBitVec.toNat = a.toUInt64.toNat + b.toUInt64.toNat := hsum_nat
  rw [hlhs, BitVec.toNat_ofInt]
  have hmod : (a.toInt + b.toInt) % ((2 ^ 64 : Nat) : Int) = a.toInt + b.toInt :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  omega

theorem expectedCalculatorScreen_has_six_lines_Impl (st : CalculatorState) :
    (expectedCalculatorScreenLines st).length = 6 := rfl

end MosaicCalculator.Model

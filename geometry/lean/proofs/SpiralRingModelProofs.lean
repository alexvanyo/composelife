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
import models.SpiralRingModel
import proofs.GeometryExtensionsModelProofs

namespace Geometry.KotlinModel

private theorem bmod_2pow32_eq_self {n : Int} (hlo : -(2 ^ 31 : Int) ≤ n) (hhi : n < (2 ^ 31 : Int)) :
    n.bmod (2 ^ 32) = n := by
  rw [Int.bmod_def]
  change (if n % (4294967296 : Int) < (4294967296 : Int) / 2 then n % (4294967296 : Int)
    else n % (4294967296 : Int) - (4294967296 : Int)) = n
  omega

private theorem ring_int32_toInt_ring (x y : Int32) (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169) :
    let ring : Int32 := (maxI32UInt (absI32UInt x.toUInt32) (absI32UInt y.toUInt32)).toInt32
    ring.toInt = max (x.toInt.natAbs : Int) (y.toInt.natAbs : Int) := by
  intro ring
  have hmin : (0x80000000 : UInt32).toInt32.toInt = -(2 ^ 31) := by decide
  have hx32 : x.toUInt32 ≠ 0x80000000 := by
    intro h
    have hi : x.toInt = (x.toUInt32.toInt32).toInt := rfl
    rw [h, hmin] at hi
    omega
  have hy32 : y.toUInt32 ≠ 0x80000000 := by
    intro h
    have hi : y.toInt = (y.toUInt32.toInt32).toInt := rfl
    rw [h, hmin] at hi
    omega
  have hax : (absI32UInt x.toUInt32).toInt32.toInt = x.toInt.natAbs := absI32UInt_toInt hx32
  have hay : (absI32UInt y.toUInt32).toInt32.toInt = y.toInt.natAbs := absI32UInt_toInt hy32
  dsimp only [ring, maxI32UInt]
  have hslt : (absI32UInt x.toUInt32).toBitVec.slt (absI32UInt y.toUInt32).toBitVec =
      decide ((x.toInt.natAbs : Int) < (y.toInt.natAbs : Int)) := by
    change decide ((absI32UInt x.toUInt32).toInt32.toInt < (absI32UInt y.toUInt32).toInt32.toInt) = _
    rw [hax, hay]
  rw [hslt]
  split
  · next h =>
    have h' : (x.toInt.natAbs : Int) < (y.toInt.natAbs : Int) := decide_eq_true_iff.mp h
    rw [hay]
    omega
  · next h =>
    have h' : ¬ ((x.toInt.natAbs : Int) < (y.toInt.natAbs : Int)) := by simpa using h
    rw [hax]
    omega

private theorem ring_exprs_exact (r : Int32) (hr1 : 1 ≤ r.toInt) (hrb : r.toInt ≤ 23169) :
    let ri := r.toInt
    let ringMin := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
    let ringMax := (2 * r + 1) * (2 * r + 1)
    let ringQ := Int32.ofBitVec ((ringMax - ringMin).toBitVec.sdiv 4#32)
    let ringQ1 := ringMin + ringQ
    let ringQ2 := ringQ1 + ringQ
    let ringQ3 := ringQ2 + ringQ
    ringMin.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) ∧
    ringMax.toInt = (2 * ri + 1) * (2 * ri + 1) ∧
    ringQ.toInt = 2 * ri ∧
    ringQ1.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 2 * ri ∧
    ringQ2.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 4 * ri ∧
    ringQ3.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 6 * ri ∧
    ringMax = ringQ3 + ringQ := by
  intro ri ringMin ringMax ringQ ringQ1 ringQ2 ringQ3
  have h1 : (1 : Int32).toInt = 1 := rfl
  have h2 : (2 : Int32).toInt = 2 := rfl
  have hmaxB : (2 * ri + 1) * (2 * ri + 1) ≤ 2147302921 := by
    have : 2 * ri + 1 ≤ 46339 := by omega
    have : 1 ≤ 2 * ri + 1 := by omega
    nlinarith
  have hminPos : 1 ≤ (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) := by
    have : 1 ≤ 2 * (ri - 1) + 1 := by omega
    nlinarith
  have hdiffEq : (2 * ri + 1) * (2 * ri + 1) - (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) = 8 * ri := by ring
  have hsub : (r - 1).toInt = ri - 1 := by
    rw [Int32.toInt_sub, h1]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have h2sub : (2 * (r - 1)).toInt = 2 * (ri - 1) := by
    rw [Int32.toInt_mul, h2, hsub]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hsideMin : (2 * (r - 1) + 1).toInt = 2 * (ri - 1) + 1 := by
    rw [Int32.toInt_add, h2sub, h1]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hringMin : ringMin.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) := by
    dsimp only [ringMin]
    rw [Int32.toInt_mul, hsideMin]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have h2r : (2 * r).toInt = 2 * ri := by
    rw [Int32.toInt_mul, h2]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hsideMax : (2 * r + 1).toInt = 2 * ri + 1 := by
    rw [Int32.toInt_add, h2r, h1]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hringMax : ringMax.toInt = (2 * ri + 1) * (2 * ri + 1) := by
    dsimp only [ringMax]
    rw [Int32.toInt_mul, hsideMax]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hdiff : (ringMax - ringMin).toInt = 8 * ri := by
    rw [Int32.toInt_sub, hringMax, hringMin, hdiffEq]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hq : ringQ.toInt = 2 * ri := by
    dsimp only [ringQ]
    change ((ringMax - ringMin).toBitVec.sdiv 4#32).toInt = 2 * ri
    rw [BitVec.toInt_sdiv]
    have h4 : (4#32 : BitVec 32).toInt = 4 := rfl
    have hbv : (ringMax - ringMin).toBitVec.toInt = (ringMax - ringMin).toInt := rfl
    rw [hbv, h4, hdiff]
    have ht : (8 * ri).tdiv 4 = 2 * ri := by
      rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
      omega
    rw [ht]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hq1 : ringQ1.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 2 * ri := by
    dsimp only [ringQ1]
    rw [Int32.toInt_add, hringMin, hq]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hq2 : ringQ2.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 4 * ri := by
    dsimp only [ringQ2]
    rw [Int32.toInt_add, hq1, hq]
    have hEq : (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 2 * ri + 2 * ri =
        (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 4 * ri := by ring
    rw [hEq]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hq3 : ringQ3.toInt = (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 6 * ri := by
    dsimp only [ringQ3]
    rw [Int32.toInt_add, hq2, hq]
    have hEq : (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 4 * ri + 2 * ri =
        (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 6 * ri := by ring
    rw [hEq]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hq3add : (ringQ3 + ringQ).toInt = (2 * ri + 1) * (2 * ri + 1) := by
    rw [Int32.toInt_add, hq3, hq]
    have hEq : (2 * (ri - 1) + 1) * (2 * (ri - 1) + 1) + 6 * ri + 2 * ri = (2 * ri + 1) * (2 * ri + 1) := by ring
    rw [hEq]
    exact bmod_2pow32_eq_self (by omega) (by omega)
  have hcheck : ringMax = ringQ3 + ringQ := by
    apply Int32.toInt.inj
    rw [hringMax, hq3add]
  exact ⟨hringMin, hringMax, hq, hq1, hq2, hq3, hcheck⟩

theorem toRingIndex_origin_Impl : toRingIndexModel 0 0 = some 0 := by
  decide

theorem toRingIndex_eq_math_Impl (x y : Int32) (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169) :
    toRingIndexModel x y = some (Int32.ofInt (toRingIndexMath x.toInt y.toInt)) ∧
    (Int32.ofInt (toRingIndexMath x.toInt y.toInt)).toInt = toRingIndexMath x.toInt y.toInt := by
  by_cases h0 : x = 0 ∧ y = 0
  · rcases h0 with ⟨rfl, rfl⟩
    refine ⟨by decide, by decide⟩
  · have hxy0 : (x == 0 && y == 0) = false := by
      cases hx0 : x == 0 <;> cases hy0 : y == 0
      · simp
      · simp
      · simp
      · exfalso
        exact h0 ⟨beq_iff_eq.mp hx0, beq_iff_eq.mp hy0⟩
    have hnotMath : ¬ (x.toInt = 0 ∧ y.toInt = 0) := by
      intro ⟨hxi, hyi⟩
      exact h0 ⟨Int32.toInt.inj hxi, Int32.toInt.inj hyi⟩
    dsimp only [toRingIndexModel, toRingIndexMath]
    rw [ite_eq_right (fun h => by simp [hxy0] at h), ite_eq_right (fun h => absurd h hnotMath)]
    set ring : Int32 := (maxI32UInt (absI32UInt x.toUInt32) (absI32UInt y.toUInt32)).toInt32
    set r : Int := max (x.toInt.natAbs : Int) (y.toInt.natAbs : Int)
    have hrVal : ring.toInt = r := ring_int32_toInt_ring x y hx hy
    have hrPos : 1 ≤ ring.toInt := by
      by_contra h
      have : x.toInt = 0 ∧ y.toInt = 0 := by omega
      exact hnotMath this
    have hrBound : ring.toInt ≤ 23169 := by omega
    rcases ring_exprs_exact ring hrPos hrBound with ⟨hmin, hmax, hq, hq1, hq2, hq3, hchk⟩
    have hminB : 1 ≤ (2 * (r - 1) + 1) * (2 * (r - 1) + 1) := by
      have : 1 ≤ 2 * (r - 1) + 1 := by omega
      nlinarith
    have hmaxB : (2 * r + 1) * (2 * r + 1) ≤ 2147302921 := by
      have : 2 * r + 1 ≤ 46339 := by omega
      have : 1 ≤ 2 * r + 1 := by omega
      nlinarith
    have hdiffB : (2 * r + 1) * (2 * r + 1) - (2 * (r - 1) + 1) * (2 * (r - 1) + 1) = 8 * r := by ring
    have hchkB :
        (((2 * ring + 1) * (2 * ring + 1) ==
          (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1) +
            Int32.ofBitVec
              (((2 * ring + 1) * (2 * ring + 1) -
                (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)).toBitVec.sdiv 4#32) +
            Int32.ofBitVec
              (((2 * ring + 1) * (2 * ring + 1) -
                (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)).toBitVec.sdiv 4#32) +
            Int32.ofBitVec
              (((2 * ring + 1) * (2 * ring + 1) -
                (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)).toBitVec.sdiv 4#32) +
            Int32.ofBitVec
              (((2 * ring + 1) * (2 * ring + 1) -
                (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)).toBitVec.sdiv 4#32)) = true) :=
      beq_iff_eq.mpr hchk
    simp only [hchkB, ↓reduceIte]
    have hnegRing : (-ring).toInt = -ring.toInt := by
      rw [Int32.toInt_neg]
      exact bmod_2pow32_eq_self (by omega) (by omega)
    change
      (let ringMin := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
       let ringQ := Int32.ofBitVec (((2 * ring + 1) * (2 * ring + 1) - ringMin).toBitVec.sdiv 4#32)
       let ringQ1 := ringMin + ringQ
       let ringQ2 := ringQ1 + ringQ
       let ringQ3 := ringQ2 + ringQ
       if (y == -ring) = true then some (ringMin + (x + ring))
       else if (x == ring) = true then some (ringQ1 + (y + ring))
       else if (y == ring) = true then some (ringQ2 + (ring - x))
       else if (x == -ring) = true then some (ringQ3 + (ring - y))
       else none) =
      some (Int32.ofInt
        (let ringMin := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
         let ringQ1 := ringMin + 2 * r
         let ringQ2 := ringQ1 + 2 * r
         let ringQ3 := ringQ2 + 2 * r
         if y.toInt = -r then ringMin + (x.toInt + r)
         else if x.toInt = r then ringQ1 + (y.toInt + r)
         else if y.toInt = r then ringQ2 + (r - x.toInt)
         else ringQ3 + (r - y.toInt))) ∧
      (Int32.ofInt
        (let ringMin := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
         let ringQ1 := ringMin + 2 * r
         let ringQ2 := ringQ1 + 2 * r
         let ringQ3 := ringQ2 + 2 * r
         if y.toInt = -r then ringMin + (x.toInt + r)
         else if x.toInt = r then ringQ1 + (y.toInt + r)
         else if y.toInt = r then ringQ2 + (r - x.toInt)
         else ringQ3 + (r - y.toInt))).toInt =
      (let ringMin := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
       let ringQ1 := ringMin + 2 * r
       let ringQ2 := ringQ1 + 2 * r
       let ringQ3 := ringQ2 + 2 * r
       if y.toInt = -r then ringMin + (x.toInt + r)
       else if x.toInt = r then ringQ1 + (y.toInt + r)
       else if y.toInt = r then ringQ2 + (r - x.toInt)
       else ringQ3 + (r - y.toInt))
    have finish :
        ∀ (res32 : Int32) (resM : Int),
          res32.toInt = resM → -(2 ^ 31 : Int) ≤ resM → resM < 2 ^ 31 →
          some res32 = some (Int32.ofInt resM) ∧ (Int32.ofInt resM).toInt = resM := by
      intro res32 resM hresInt hlo hhi
      have hof : Int32.ofInt resM = res32 := Int32.toInt.inj (by
        rw [hresInt, Int32.toInt_ofInt]
        exact bmod_2pow32_eq_self hlo hhi)
      exact ⟨congrArg some hof.symm, by rw [hof, hresInt]⟩
    by_cases hyNeg : y = -ring
    · have hyNegM : y.toInt = -r := by rw [← hrVal, hyNeg, hnegRing]
      have hyNegB : (y == -ring) = true := beq_iff_eq.mpr hyNeg
      simp only [hyNegB, hyNegM, ↓reduceIte]
      set res32 := ((2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)) + (x + ring)
      set resM := (2 * (r - 1) + 1) * (2 * (r - 1) + 1) + (x.toInt + r)
      have hxr : (x + ring).toInt = x.toInt + ring.toInt := by
        rw [Int32.toInt_add]
        exact bmod_2pow32_eq_self (by omega) (by omega)
      have hresInt : res32.toInt = resM := by
        dsimp only [res32, resM]
        rw [Int32.toInt_add, hmin, hxr, hrVal]
        exact bmod_2pow32_eq_self (by omega) (by omega)
      exact finish res32 resM hresInt (by omega) (by omega)
    · have hyNegM : y.toInt ≠ -r := fun h => hyNeg (Int32.toInt.inj (by rw [hnegRing, hrVal]; exact h))
      have hyNegB : (y == -ring) = false := beq_false_of_ne hyNeg
      simp only [hyNegB, hyNegM, ↓reduceIte, Bool.false_eq_true]
      by_cases hxPos : x = ring
      · have hxPosM : x.toInt = r := by rw [← hrVal, hxPos]
        have hxPosB : (x == ring) = true := beq_iff_eq.mpr hxPos
        simp only [hxPosB, hxPosM, ↓reduceIte]
        set ringMin := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
        set ringQ := Int32.ofBitVec (((2 * ring + 1) * (2 * ring + 1) - ringMin).toBitVec.sdiv 4#32)
        set ringQ1 := ringMin + ringQ
        set res32 := ringQ1 + (y + ring)
        set resM := ((2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 2 * r) + (y.toInt + r)
        have hyr : (y + ring).toInt = y.toInt + ring.toInt := by
          rw [Int32.toInt_add]
          exact bmod_2pow32_eq_self (by omega) (by omega)
        have hresInt : res32.toInt = resM := by
          dsimp only [res32, resM]
          rw [Int32.toInt_add, hq1, hyr, hrVal]
          exact bmod_2pow32_eq_self (by omega) (by omega)
        exact finish res32 resM hresInt (by omega) (by omega)
      · have hxPosM : x.toInt ≠ r := fun h => hxPos (Int32.toInt.inj (by rw [hrVal]; exact h))
        have hxPosB : (x == ring) = false := beq_false_of_ne hxPos
        simp only [hxPosB, hxPosM, ↓reduceIte, Bool.false_eq_true]
        by_cases hyPos : y = ring
        · have hyPosM : y.toInt = r := by rw [← hrVal, hyPos]
          have hyPosB : (y == ring) = true := beq_iff_eq.mpr hyPos
          simp only [hyPosB, hyPosM, ↓reduceIte]
          set ringMin := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
          set ringQ := Int32.ofBitVec (((2 * ring + 1) * (2 * ring + 1) - ringMin).toBitVec.sdiv 4#32)
          set ringQ2 := (ringMin + ringQ) + ringQ
          set res32 := ringQ2 + (ring - x)
          set resM := (((2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 2 * r) + 2 * r) + (r - x.toInt)
          have hrx : (ring - x).toInt = ring.toInt - x.toInt := by
            rw [Int32.toInt_sub]
            exact bmod_2pow32_eq_self (by omega) (by omega)
          have hresInt : res32.toInt = resM := by
            dsimp only [res32, resM]
            rw [Int32.toInt_add, hq2, hrx, hrVal]
            have hEq : (2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 4 * r =
                ((2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 2 * r) + 2 * r := by ring
            rw [← hEq]
            exact bmod_2pow32_eq_self (by omega) (by omega)
          exact finish res32 resM hresInt (by omega) (by omega)
        · have hyPosM : y.toInt ≠ r := fun h => hyPos (Int32.toInt.inj (by rw [hrVal]; exact h))
          have hyPosB : (y == ring) = false := beq_false_of_ne hyPos
          simp only [hyPosB, hyPosM, ↓reduceIte, Bool.false_eq_true]
          have hxNeg : x = -ring := Int32.toInt.inj (by rw [hnegRing]; omega)
          have hxNegB : (x == -ring) = true := beq_iff_eq.mpr hxNeg
          simp only [hxNegB, ↓reduceIte]
          set ringMin := (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
          set ringQ := Int32.ofBitVec (((2 * ring + 1) * (2 * ring + 1) - ringMin).toBitVec.sdiv 4#32)
          set ringQ3 := ((ringMin + ringQ) + ringQ) + ringQ
          set res32 := ringQ3 + (ring - y)
          set resM := ((((2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 2 * r) + 2 * r) + 2 * r) + (r - y.toInt)
          have hry : (ring - y).toInt = ring.toInt - y.toInt := by
            rw [Int32.toInt_sub]
            exact bmod_2pow32_eq_self (by omega) (by omega)
          have hresInt : res32.toInt = resM := by
            dsimp only [res32, resM]
            rw [Int32.toInt_add, hq3, hry, hrVal]
            have hEq : (2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 6 * r =
                (((2 * (r - 1) + 1) * (2 * (r - 1) + 1) + 2 * r) + 2 * r) + 2 * r := by ring
            rw [← hEq]
            exact bmod_2pow32_eq_self (by omega) (by omega)
          exact finish res32 resM hresInt (by omega) (by omega)

private def ringEdgeExpr (r x y : Int) : Int :=
  let m := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
  if y = -r then m + (x + r)
  else if x = r then (m + 2 * r) + (y + r)
  else if y = r then ((m + 2 * r) + 2 * r) + (r - x)
  else (((m + 2 * r) + 2 * r) + 2 * r) + (r - y)

private theorem toRingIndexMath_eq_ringEdgeExpr {x y : Int} (hne : ¬ (x = 0 ∧ y = 0)) :
    toRingIndexMath x y = ringEdgeExpr (max x.natAbs y.natAbs) x y := by
  dsimp only [toRingIndexMath, ringEdgeExpr]
  rw [ite_eq_right (fun h => absurd h hne)]

theorem toRingIndexMath_bounds {x y : Int} (hne : ¬ (x = 0 ∧ y = 0)) :
    let r : Int := max x.natAbs y.natAbs
    (2 * (r - 1) + 1) * (2 * (r - 1) + 1) ≤ toRingIndexMath x y ∧
    toRingIndexMath x y < (2 * r + 1) * (2 * r + 1) := by
  rw [toRingIndexMath_eq_ringEdgeExpr hne]
  set r : Int := max x.natAbs y.natAbs
  have hr : 1 ≤ r := by omega
  have hmax : x = r ∨ x = -r ∨ y = r ∨ y = -r := by omega
  have hxlo : -r ≤ x := by omega
  have hxhi : x ≤ r := by omega
  have hylo : -r ≤ y := by omega
  have hyhi : y ≤ r := by omega
  have hsq : (2 * r + 1) * (2 * r + 1) - (2 * (r - 1) + 1) * (2 * (r - 1) + 1) = 8 * r := by ring
  dsimp only [ringEdgeExpr]
  set m : Int := (2 * (r - 1) + 1) * (2 * (r - 1) + 1)
  change
    m ≤ (if y = -r then m + (x + r)
         else if x = r then (m + 2 * r) + (y + r)
         else if y = r then ((m + 2 * r) + 2 * r) + (r - x)
         else (((m + 2 * r) + 2 * r) + 2 * r) + (r - y)) ∧
    (if y = -r then m + (x + r)
     else if x = r then (m + 2 * r) + (y + r)
     else if y = r then ((m + 2 * r) + 2 * r) + (r - x)
     else (((m + 2 * r) + 2 * r) + 2 * r) + (r - y)) < (2 * r + 1) * (2 * r + 1)
  split_ifs <;> constructor <;> omega

theorem toRingIndex_noCheckFail_and_shellBounds_Impl
    (x y : Int32) (hx : x.toInt.natAbs ≤ 23169) (hy : y.toInt.natAbs ≤ 23169) :
    ∃ idx : Int32,
      toRingIndexModel x y = some idx ∧
      idx.toInt = toRingIndexMath x.toInt y.toInt ∧
      (x = 0 ∧ y = 0 → idx = 0) ∧
      (let r : Int := max x.toInt.natAbs y.toInt.natAbs
       1 ≤ r →
       (2 * (r - 1) + 1) * (2 * (r - 1) + 1) ≤ idx.toInt ∧
       idx.toInt < (2 * r + 1) * (2 * r + 1)) := by
  rcases toRingIndex_eq_math_Impl x y hx hy with ⟨hm, hi⟩
  refine ⟨Int32.ofInt (toRingIndexMath x.toInt y.toInt), hm, hi, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    decide
  · intro r hr
    have hne : ¬ (x.toInt = 0 ∧ y.toInt = 0) := by omega
    rcases toRingIndexMath_bounds hne with ⟨hlo, hhi⟩
    rw [hi]
    exact ⟨hlo, hhi⟩

private theorem shell_eq_of_math_eq {x1 y1 x2 y2 : Int}
    (heq : toRingIndexMath x1 y1 = toRingIndexMath x2 y2) :
    max x1.natAbs y1.natAbs = max x2.natAbs y2.natAbs := by
  by_cases h1 : x1 = 0 ∧ y1 = 0 <;> by_cases h2 : x2 = 0 ∧ y2 = 0
  · rcases h1 with ⟨rfl, rfl⟩; rcases h2 with ⟨rfl, rfl⟩; rfl
  · rcases h1 with ⟨rfl, rfl⟩
    have h0 : toRingIndexMath 0 0 = 0 := by decide
    rcases toRingIndexMath_bounds h2 with ⟨hlo, _⟩
    set r2 : Int := max x2.natAbs y2.natAbs
    have hr2 : 1 ≤ r2 := by omega
    have hlo' : (2 * (r2 - 1) + 1) * (2 * (r2 - 1) + 1) ≤ toRingIndexMath x2 y2 := hlo
    have hpos : 1 ≤ toRingIndexMath x2 y2 := by nlinarith
    omega
  · rcases h2 with ⟨rfl, rfl⟩
    have h0 : toRingIndexMath 0 0 = 0 := by decide
    rcases toRingIndexMath_bounds h1 with ⟨hlo, _⟩
    set r1 : Int := max x1.natAbs y1.natAbs
    have hr1 : 1 ≤ r1 := by omega
    have hlo' : (2 * (r1 - 1) + 1) * (2 * (r1 - 1) + 1) ≤ toRingIndexMath x1 y1 := hlo
    have hpos : 1 ≤ toRingIndexMath x1 y1 := by nlinarith
    omega
  · have hb1 := toRingIndexMath_bounds h1
    have hb2 := toRingIndexMath_bounds h2
    rw [heq] at hb1
    set r1 : Int := max x1.natAbs y1.natAbs
    set r2 : Int := max x2.natAbs y2.natAbs
    have hr1Pos : 1 ≤ r1 := by omega
    have hr2Pos : 1 ≤ r2 := by omega
    have hb1' : (2 * (r1 - 1) + 1) * (2 * (r1 - 1) + 1) ≤ toRingIndexMath x2 y2 ∧
        toRingIndexMath x2 y2 < (2 * r1 + 1) * (2 * r1 + 1) := hb1
    have hb2' : (2 * (r2 - 1) + 1) * (2 * (r2 - 1) + 1) ≤ toRingIndexMath x2 y2 ∧
        toRingIndexMath x2 y2 < (2 * r2 + 1) * (2 * r2 + 1) := hb2
    by_contra hne
    rcases (by omega : r1 < r2 ∨ r2 < r1) with hlt | hgt
    · have hsq : (2 * r1 + 1) * (2 * r1 + 1) ≤ (2 * (r2 - 1) + 1) * (2 * (r2 - 1) + 1) := by nlinarith
      omega
    · have hsq : (2 * r2 + 1) * (2 * r2 + 1) ≤ (2 * (r1 - 1) + 1) * (2 * (r1 - 1) + 1) := by nlinarith
      omega

private theorem edge_injective_core (m r x1 y1 x2 y2 : Int) (hr : 1 ≤ r)
    (hx1lo : -r ≤ x1) (hx1hi : x1 ≤ r) (hy1lo : -r ≤ y1) (hy1hi : y1 ≤ r)
    (hx2lo : -r ≤ x2) (hx2hi : x2 ≤ r) (hy2lo : -r ≤ y2) (hy2hi : y2 ≤ r)
    (hb1 : x1 = r ∨ x1 = -r ∨ y1 = r ∨ y1 = -r)
    (hb2 : x2 = r ∨ x2 = -r ∨ y2 = r ∨ y2 = -r)
    (heq :
      (if y1 = -r then m + (x1 + r)
       else if x1 = r then (m + 2 * r) + (y1 + r)
       else if y1 = r then ((m + 2 * r) + 2 * r) + (r - x1)
       else (((m + 2 * r) + 2 * r) + 2 * r) + (r - y1)) =
      (if y2 = -r then m + (x2 + r)
       else if x2 = r then (m + 2 * r) + (y2 + r)
       else if y2 = r then ((m + 2 * r) + 2 * r) + (r - x2)
       else (((m + 2 * r) + 2 * r) + 2 * r) + (r - y2))) :
    x1 = x2 ∧ y1 = y2 := by
  split_ifs at heq <;> constructor <;> omega

theorem toRingIndexMath_injective {x1 y1 x2 y2 : Int}
    (heq : toRingIndexMath x1 y1 = toRingIndexMath x2 y2) :
    x1 = x2 ∧ y1 = y2 := by
  have hrNat := shell_eq_of_math_eq heq
  by_cases hr0 : max x1.natAbs y1.natAbs = 0
  · omega
  · have hr1 : ¬ (x1 = 0 ∧ y1 = 0) := by omega
    have hr2 : ¬ (x2 = 0 ∧ y2 = 0) := by omega
    set r : Int := max x1.natAbs y1.natAbs
    have hrPos : 1 ≤ r := by omega
    have hr2Eq : (max x2.natAbs y2.natAbs : Int) = r := by omega
    have hx1lo : -r ≤ x1 := by omega
    have hx1hi : x1 ≤ r := by omega
    have hy1lo : -r ≤ y1 := by omega
    have hy1hi : y1 ≤ r := by omega
    have hx2lo : -r ≤ x2 := by omega
    have hx2hi : x2 ≤ r := by omega
    have hy2lo : -r ≤ y2 := by omega
    have hy2hi : y2 ≤ r := by omega
    have hb1 : x1 = r ∨ x1 = -r ∨ y1 = r ∨ y1 = -r := by omega
    have hb2 : x2 = r ∨ x2 = -r ∨ y2 = r ∨ y2 = -r := by omega
    rw [toRingIndexMath_eq_ringEdgeExpr hr1, toRingIndexMath_eq_ringEdgeExpr hr2] at heq
    have heq' : ringEdgeExpr r x1 y1 = ringEdgeExpr r x2 y2 := by
      have : ringEdgeExpr (max x1.natAbs y1.natAbs : Int) x1 y1 =
          ringEdgeExpr (max x2.natAbs y2.natAbs : Int) x2 y2 := heq
      rw [hr2Eq] at this
      exact this
    dsimp only [ringEdgeExpr] at heq'
    exact edge_injective_core ((2 * (r - 1) + 1) * (2 * (r - 1) + 1)) r x1 y1 x2 y2
      hrPos hx1lo hx1hi hy1lo hy1hi hx2lo hx2hi hy2lo hy2hi hb1 hb2 heq'

theorem toRingIndex_injective_Impl
    (x1 y1 x2 y2 : Int32) (idx : Int32)
    (hx1 : x1.toInt.natAbs ≤ 23169) (hy1 : y1.toInt.natAbs ≤ 23169)
    (hx2 : x2.toInt.natAbs ≤ 23169) (hy2 : y2.toInt.natAbs ≤ 23169)
    (h1 : toRingIndexModel x1 y1 = some idx)
    (h2 : toRingIndexModel x2 y2 = some idx) :
    x1 = x2 ∧ y1 = y2 := by
  rcases toRingIndex_eq_math_Impl x1 y1 hx1 hy1 with ⟨hm1, hi1⟩
  rcases toRingIndex_eq_math_Impl x2 y2 hx2 hy2 with ⟨hm2, hi2⟩
  rw [h1] at hm1
  rw [h2] at hm2
  injection hm1 with hi1Eq
  injection hm2 with hi2Eq
  have hmathEq : toRingIndexMath x1.toInt y1.toInt = toRingIndexMath x2.toInt y2.toInt := by
    have ha : idx.toInt = toRingIndexMath x1.toInt y1.toInt := by rw [hi1Eq, hi1]
    have hb : idx.toInt = toRingIndexMath x2.toInt y2.toInt := by rw [hi2Eq, hi2]
    exact ha.symm.trans hb
  rcases toRingIndexMath_injective hmathEq with ⟨hxEq, hyEq⟩
  exact ⟨Int32.toInt.inj hxEq, Int32.toInt.inj hyEq⟩

end Geometry.KotlinModel

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


import Std.Tactic.BVDecide
import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.HashLife
import Algorithm.HashLifeEquivalence
import AlgorithmDefs
import proofs.SemanticModelProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

-- =========================================================================
-- Conway Rule as a Bit-Vector Circuit
-- =========================================================================

/--
Conway's rule on a center cell and its eight neighbors, phrased with a 4-bit counter
so that it can be bit-blasted.
-/
def lifeB (c b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  let n : BitVec 4 := (if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0) +
    (if b4 then 1 else 0) + (if b5 then 1 else 0) + (if b6 then 1 else 0) + (if b7 then 1 else 0) +
    (if b8 then 1 else 0)
  n == 3 || (n == 2 && c)

theorem lifeRule_eq_lifeB (c b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    lifeRule c (b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat + b8.toNat) =
    lifeB c b1 b2 b3 b4 b5 b6 b7 b8 := by
  revert c b1 b2 b3 b4 b5 b6 b7 b8
  decide

theorem nextGenAt_eq_lifeB (f : ℤ → ℤ → Bool) (x y : ℤ) :
    nextGenAt f x y = lifeB (f x y) (f (x - 1) (y - 1)) (f x (y - 1)) (f (x + 1) (y - 1))
      (f (x - 1) y) (f (x + 1) y) (f (x - 1) (y + 1)) (f x (y + 1)) (f (x + 1) (y + 1)) := by
  unfold nextGenAt
  rw [neighborCountAt_eq, lifeRule_eq_lifeB]

-- =========================================================================
-- Level 4 Stepping Kernel (16x16 -> central 8x8, one generation)
-- =========================================================================

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/--
Bit-level specification of `computeLevel4NextGen16x16UInt`: every one of the 64 output bits is
Conway's rule applied to the corresponding 3x3 neighborhood of the 16x16 input. Generated
mechanically and discharged by bit-blasting.
-/
theorem level4_kernel_bits (a b c d : UInt64) :
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 0 =
      lifeB (a.toBitVec.getLsbD 48) (a.toBitVec.getLsbD 15) (a.toBitVec.getLsbD 26) (a.toBitVec.getLsbD 27)
          (a.toBitVec.getLsbD 37) (a.toBitVec.getLsbD 49) (a.toBitVec.getLsbD 39) (a.toBitVec.getLsbD 50)
          (a.toBitVec.getLsbD 51) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 1 =
      lifeB (a.toBitVec.getLsbD 49) (a.toBitVec.getLsbD 26) (a.toBitVec.getLsbD 27) (a.toBitVec.getLsbD 30)
          (a.toBitVec.getLsbD 48) (a.toBitVec.getLsbD 52) (a.toBitVec.getLsbD 50) (a.toBitVec.getLsbD 51)
          (a.toBitVec.getLsbD 54) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 4 =
      lifeB (a.toBitVec.getLsbD 52) (a.toBitVec.getLsbD 27) (a.toBitVec.getLsbD 30) (a.toBitVec.getLsbD 31)
          (a.toBitVec.getLsbD 49) (a.toBitVec.getLsbD 53) (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 54)
          (a.toBitVec.getLsbD 55) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 5 =
      lifeB (a.toBitVec.getLsbD 53) (a.toBitVec.getLsbD 30) (a.toBitVec.getLsbD 31) (b.toBitVec.getLsbD 10)
          (a.toBitVec.getLsbD 52) (b.toBitVec.getLsbD 32) (a.toBitVec.getLsbD 54) (a.toBitVec.getLsbD 55)
          (b.toBitVec.getLsbD 34) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 16 =
      lifeB (b.toBitVec.getLsbD 32) (a.toBitVec.getLsbD 31) (b.toBitVec.getLsbD 10) (b.toBitVec.getLsbD 11)
          (a.toBitVec.getLsbD 53) (b.toBitVec.getLsbD 33) (a.toBitVec.getLsbD 55) (b.toBitVec.getLsbD 34)
          (b.toBitVec.getLsbD 35) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 17 =
      lifeB (b.toBitVec.getLsbD 33) (b.toBitVec.getLsbD 10) (b.toBitVec.getLsbD 11) (b.toBitVec.getLsbD 14)
          (b.toBitVec.getLsbD 32) (b.toBitVec.getLsbD 36) (b.toBitVec.getLsbD 34) (b.toBitVec.getLsbD 35)
          (b.toBitVec.getLsbD 38) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 20 =
      lifeB (b.toBitVec.getLsbD 36) (b.toBitVec.getLsbD 11) (b.toBitVec.getLsbD 14) (b.toBitVec.getLsbD 15)
          (b.toBitVec.getLsbD 33) (b.toBitVec.getLsbD 37) (b.toBitVec.getLsbD 35) (b.toBitVec.getLsbD 38)
          (b.toBitVec.getLsbD 39) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 21 =
      lifeB (b.toBitVec.getLsbD 37) (b.toBitVec.getLsbD 14) (b.toBitVec.getLsbD 15) (b.toBitVec.getLsbD 26)
          (b.toBitVec.getLsbD 36) (b.toBitVec.getLsbD 48) (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 39)
          (b.toBitVec.getLsbD 50) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 2 =
      lifeB (a.toBitVec.getLsbD 50) (a.toBitVec.getLsbD 37) (a.toBitVec.getLsbD 48) (a.toBitVec.getLsbD 49)
          (a.toBitVec.getLsbD 39) (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 45) (a.toBitVec.getLsbD 56)
          (a.toBitVec.getLsbD 57) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 3 =
      lifeB (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 48) (a.toBitVec.getLsbD 49) (a.toBitVec.getLsbD 52)
          (a.toBitVec.getLsbD 50) (a.toBitVec.getLsbD 54) (a.toBitVec.getLsbD 56) (a.toBitVec.getLsbD 57)
          (a.toBitVec.getLsbD 60) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 6 =
      lifeB (a.toBitVec.getLsbD 54) (a.toBitVec.getLsbD 49) (a.toBitVec.getLsbD 52) (a.toBitVec.getLsbD 53)
          (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 55) (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 60)
          (a.toBitVec.getLsbD 61) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 7 =
      lifeB (a.toBitVec.getLsbD 55) (a.toBitVec.getLsbD 52) (a.toBitVec.getLsbD 53) (b.toBitVec.getLsbD 32)
          (a.toBitVec.getLsbD 54) (b.toBitVec.getLsbD 34) (a.toBitVec.getLsbD 60) (a.toBitVec.getLsbD 61)
          (b.toBitVec.getLsbD 40) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 18 =
      lifeB (b.toBitVec.getLsbD 34) (a.toBitVec.getLsbD 53) (b.toBitVec.getLsbD 32) (b.toBitVec.getLsbD 33)
          (a.toBitVec.getLsbD 55) (b.toBitVec.getLsbD 35) (a.toBitVec.getLsbD 61) (b.toBitVec.getLsbD 40)
          (b.toBitVec.getLsbD 41) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 19 =
      lifeB (b.toBitVec.getLsbD 35) (b.toBitVec.getLsbD 32) (b.toBitVec.getLsbD 33) (b.toBitVec.getLsbD 36)
          (b.toBitVec.getLsbD 34) (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 40) (b.toBitVec.getLsbD 41)
          (b.toBitVec.getLsbD 44) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 22 =
      lifeB (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 33) (b.toBitVec.getLsbD 36) (b.toBitVec.getLsbD 37)
          (b.toBitVec.getLsbD 35) (b.toBitVec.getLsbD 39) (b.toBitVec.getLsbD 41) (b.toBitVec.getLsbD 44)
          (b.toBitVec.getLsbD 45) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 23 =
      lifeB (b.toBitVec.getLsbD 39) (b.toBitVec.getLsbD 36) (b.toBitVec.getLsbD 37) (b.toBitVec.getLsbD 48)
          (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 50) (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 45)
          (b.toBitVec.getLsbD 56) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 8 =
      lifeB (a.toBitVec.getLsbD 56) (a.toBitVec.getLsbD 39) (a.toBitVec.getLsbD 50) (a.toBitVec.getLsbD 51)
          (a.toBitVec.getLsbD 45) (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 47) (a.toBitVec.getLsbD 58)
          (a.toBitVec.getLsbD 59) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 9 =
      lifeB (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 50) (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 54)
          (a.toBitVec.getLsbD 56) (a.toBitVec.getLsbD 60) (a.toBitVec.getLsbD 58) (a.toBitVec.getLsbD 59)
          (a.toBitVec.getLsbD 62) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 12 =
      lifeB (a.toBitVec.getLsbD 60) (a.toBitVec.getLsbD 51) (a.toBitVec.getLsbD 54) (a.toBitVec.getLsbD 55)
          (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 61) (a.toBitVec.getLsbD 59) (a.toBitVec.getLsbD 62)
          (a.toBitVec.getLsbD 63) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 13 =
      lifeB (a.toBitVec.getLsbD 61) (a.toBitVec.getLsbD 54) (a.toBitVec.getLsbD 55) (b.toBitVec.getLsbD 34)
          (a.toBitVec.getLsbD 60) (b.toBitVec.getLsbD 40) (a.toBitVec.getLsbD 62) (a.toBitVec.getLsbD 63)
          (b.toBitVec.getLsbD 42) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 24 =
      lifeB (b.toBitVec.getLsbD 40) (a.toBitVec.getLsbD 55) (b.toBitVec.getLsbD 34) (b.toBitVec.getLsbD 35)
          (a.toBitVec.getLsbD 61) (b.toBitVec.getLsbD 41) (a.toBitVec.getLsbD 63) (b.toBitVec.getLsbD 42)
          (b.toBitVec.getLsbD 43) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 25 =
      lifeB (b.toBitVec.getLsbD 41) (b.toBitVec.getLsbD 34) (b.toBitVec.getLsbD 35) (b.toBitVec.getLsbD 38)
          (b.toBitVec.getLsbD 40) (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 42) (b.toBitVec.getLsbD 43)
          (b.toBitVec.getLsbD 46) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 28 =
      lifeB (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 35) (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 39)
          (b.toBitVec.getLsbD 41) (b.toBitVec.getLsbD 45) (b.toBitVec.getLsbD 43) (b.toBitVec.getLsbD 46)
          (b.toBitVec.getLsbD 47) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 29 =
      lifeB (b.toBitVec.getLsbD 45) (b.toBitVec.getLsbD 38) (b.toBitVec.getLsbD 39) (b.toBitVec.getLsbD 50)
          (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 56) (b.toBitVec.getLsbD 46) (b.toBitVec.getLsbD 47)
          (b.toBitVec.getLsbD 58) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 10 =
      lifeB (a.toBitVec.getLsbD 58) (a.toBitVec.getLsbD 45) (a.toBitVec.getLsbD 56) (a.toBitVec.getLsbD 57)
          (a.toBitVec.getLsbD 47) (a.toBitVec.getLsbD 59) (c.toBitVec.getLsbD 5) (c.toBitVec.getLsbD 16)
          (c.toBitVec.getLsbD 17) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 11 =
      lifeB (a.toBitVec.getLsbD 59) (a.toBitVec.getLsbD 56) (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 60)
          (a.toBitVec.getLsbD 58) (a.toBitVec.getLsbD 62) (c.toBitVec.getLsbD 16) (c.toBitVec.getLsbD 17)
          (c.toBitVec.getLsbD 20) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 14 =
      lifeB (a.toBitVec.getLsbD 62) (a.toBitVec.getLsbD 57) (a.toBitVec.getLsbD 60) (a.toBitVec.getLsbD 61)
          (a.toBitVec.getLsbD 59) (a.toBitVec.getLsbD 63) (c.toBitVec.getLsbD 17) (c.toBitVec.getLsbD 20)
          (c.toBitVec.getLsbD 21) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 15 =
      lifeB (a.toBitVec.getLsbD 63) (a.toBitVec.getLsbD 60) (a.toBitVec.getLsbD 61) (b.toBitVec.getLsbD 40)
          (a.toBitVec.getLsbD 62) (b.toBitVec.getLsbD 42) (c.toBitVec.getLsbD 20) (c.toBitVec.getLsbD 21)
          (d.toBitVec.getLsbD 0) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 26 =
      lifeB (b.toBitVec.getLsbD 42) (a.toBitVec.getLsbD 61) (b.toBitVec.getLsbD 40) (b.toBitVec.getLsbD 41)
          (a.toBitVec.getLsbD 63) (b.toBitVec.getLsbD 43) (c.toBitVec.getLsbD 21) (d.toBitVec.getLsbD 0)
          (d.toBitVec.getLsbD 1) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 27 =
      lifeB (b.toBitVec.getLsbD 43) (b.toBitVec.getLsbD 40) (b.toBitVec.getLsbD 41) (b.toBitVec.getLsbD 44)
          (b.toBitVec.getLsbD 42) (b.toBitVec.getLsbD 46) (d.toBitVec.getLsbD 0) (d.toBitVec.getLsbD 1)
          (d.toBitVec.getLsbD 4) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 30 =
      lifeB (b.toBitVec.getLsbD 46) (b.toBitVec.getLsbD 41) (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 45)
          (b.toBitVec.getLsbD 43) (b.toBitVec.getLsbD 47) (d.toBitVec.getLsbD 1) (d.toBitVec.getLsbD 4)
          (d.toBitVec.getLsbD 5) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 31 =
      lifeB (b.toBitVec.getLsbD 47) (b.toBitVec.getLsbD 44) (b.toBitVec.getLsbD 45) (b.toBitVec.getLsbD 56)
          (b.toBitVec.getLsbD 46) (b.toBitVec.getLsbD 58) (d.toBitVec.getLsbD 4) (d.toBitVec.getLsbD 5)
          (d.toBitVec.getLsbD 16) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 32 =
      lifeB (c.toBitVec.getLsbD 16) (a.toBitVec.getLsbD 47) (a.toBitVec.getLsbD 58) (a.toBitVec.getLsbD 59)
          (c.toBitVec.getLsbD 5) (c.toBitVec.getLsbD 17) (c.toBitVec.getLsbD 7) (c.toBitVec.getLsbD 18)
          (c.toBitVec.getLsbD 19) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 33 =
      lifeB (c.toBitVec.getLsbD 17) (a.toBitVec.getLsbD 58) (a.toBitVec.getLsbD 59) (a.toBitVec.getLsbD 62)
          (c.toBitVec.getLsbD 16) (c.toBitVec.getLsbD 20) (c.toBitVec.getLsbD 18) (c.toBitVec.getLsbD 19)
          (c.toBitVec.getLsbD 22) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 36 =
      lifeB (c.toBitVec.getLsbD 20) (a.toBitVec.getLsbD 59) (a.toBitVec.getLsbD 62) (a.toBitVec.getLsbD 63)
          (c.toBitVec.getLsbD 17) (c.toBitVec.getLsbD 21) (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 22)
          (c.toBitVec.getLsbD 23) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 37 =
      lifeB (c.toBitVec.getLsbD 21) (a.toBitVec.getLsbD 62) (a.toBitVec.getLsbD 63) (b.toBitVec.getLsbD 42)
          (c.toBitVec.getLsbD 20) (d.toBitVec.getLsbD 0) (c.toBitVec.getLsbD 22) (c.toBitVec.getLsbD 23)
          (d.toBitVec.getLsbD 2) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 48 =
      lifeB (d.toBitVec.getLsbD 0) (a.toBitVec.getLsbD 63) (b.toBitVec.getLsbD 42) (b.toBitVec.getLsbD 43)
          (c.toBitVec.getLsbD 21) (d.toBitVec.getLsbD 1) (c.toBitVec.getLsbD 23) (d.toBitVec.getLsbD 2)
          (d.toBitVec.getLsbD 3) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 49 =
      lifeB (d.toBitVec.getLsbD 1) (b.toBitVec.getLsbD 42) (b.toBitVec.getLsbD 43) (b.toBitVec.getLsbD 46)
          (d.toBitVec.getLsbD 0) (d.toBitVec.getLsbD 4) (d.toBitVec.getLsbD 2) (d.toBitVec.getLsbD 3)
          (d.toBitVec.getLsbD 6) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 52 =
      lifeB (d.toBitVec.getLsbD 4) (b.toBitVec.getLsbD 43) (b.toBitVec.getLsbD 46) (b.toBitVec.getLsbD 47)
          (d.toBitVec.getLsbD 1) (d.toBitVec.getLsbD 5) (d.toBitVec.getLsbD 3) (d.toBitVec.getLsbD 6)
          (d.toBitVec.getLsbD 7) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 53 =
      lifeB (d.toBitVec.getLsbD 5) (b.toBitVec.getLsbD 46) (b.toBitVec.getLsbD 47) (b.toBitVec.getLsbD 58)
          (d.toBitVec.getLsbD 4) (d.toBitVec.getLsbD 16) (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 7)
          (d.toBitVec.getLsbD 18) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 34 =
      lifeB (c.toBitVec.getLsbD 18) (c.toBitVec.getLsbD 5) (c.toBitVec.getLsbD 16) (c.toBitVec.getLsbD 17)
          (c.toBitVec.getLsbD 7) (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 13) (c.toBitVec.getLsbD 24)
          (c.toBitVec.getLsbD 25) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 35 =
      lifeB (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 16) (c.toBitVec.getLsbD 17) (c.toBitVec.getLsbD 20)
          (c.toBitVec.getLsbD 18) (c.toBitVec.getLsbD 22) (c.toBitVec.getLsbD 24) (c.toBitVec.getLsbD 25)
          (c.toBitVec.getLsbD 28) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 38 =
      lifeB (c.toBitVec.getLsbD 22) (c.toBitVec.getLsbD 17) (c.toBitVec.getLsbD 20) (c.toBitVec.getLsbD 21)
          (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 23) (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 28)
          (c.toBitVec.getLsbD 29) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 39 =
      lifeB (c.toBitVec.getLsbD 23) (c.toBitVec.getLsbD 20) (c.toBitVec.getLsbD 21) (d.toBitVec.getLsbD 0)
          (c.toBitVec.getLsbD 22) (d.toBitVec.getLsbD 2) (c.toBitVec.getLsbD 28) (c.toBitVec.getLsbD 29)
          (d.toBitVec.getLsbD 8) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 50 =
      lifeB (d.toBitVec.getLsbD 2) (c.toBitVec.getLsbD 21) (d.toBitVec.getLsbD 0) (d.toBitVec.getLsbD 1)
          (c.toBitVec.getLsbD 23) (d.toBitVec.getLsbD 3) (c.toBitVec.getLsbD 29) (d.toBitVec.getLsbD 8)
          (d.toBitVec.getLsbD 9) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 51 =
      lifeB (d.toBitVec.getLsbD 3) (d.toBitVec.getLsbD 0) (d.toBitVec.getLsbD 1) (d.toBitVec.getLsbD 4)
          (d.toBitVec.getLsbD 2) (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 8) (d.toBitVec.getLsbD 9)
          (d.toBitVec.getLsbD 12) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 54 =
      lifeB (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 1) (d.toBitVec.getLsbD 4) (d.toBitVec.getLsbD 5)
          (d.toBitVec.getLsbD 3) (d.toBitVec.getLsbD 7) (d.toBitVec.getLsbD 9) (d.toBitVec.getLsbD 12)
          (d.toBitVec.getLsbD 13) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 55 =
      lifeB (d.toBitVec.getLsbD 7) (d.toBitVec.getLsbD 4) (d.toBitVec.getLsbD 5) (d.toBitVec.getLsbD 16)
          (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 18) (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 13)
          (d.toBitVec.getLsbD 24) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 40 =
      lifeB (c.toBitVec.getLsbD 24) (c.toBitVec.getLsbD 7) (c.toBitVec.getLsbD 18) (c.toBitVec.getLsbD 19)
          (c.toBitVec.getLsbD 13) (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 15) (c.toBitVec.getLsbD 26)
          (c.toBitVec.getLsbD 27) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 41 =
      lifeB (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 18) (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 22)
          (c.toBitVec.getLsbD 24) (c.toBitVec.getLsbD 28) (c.toBitVec.getLsbD 26) (c.toBitVec.getLsbD 27)
          (c.toBitVec.getLsbD 30) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 44 =
      lifeB (c.toBitVec.getLsbD 28) (c.toBitVec.getLsbD 19) (c.toBitVec.getLsbD 22) (c.toBitVec.getLsbD 23)
          (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 29) (c.toBitVec.getLsbD 27) (c.toBitVec.getLsbD 30)
          (c.toBitVec.getLsbD 31) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 45 =
      lifeB (c.toBitVec.getLsbD 29) (c.toBitVec.getLsbD 22) (c.toBitVec.getLsbD 23) (d.toBitVec.getLsbD 2)
          (c.toBitVec.getLsbD 28) (d.toBitVec.getLsbD 8) (c.toBitVec.getLsbD 30) (c.toBitVec.getLsbD 31)
          (d.toBitVec.getLsbD 10) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 56 =
      lifeB (d.toBitVec.getLsbD 8) (c.toBitVec.getLsbD 23) (d.toBitVec.getLsbD 2) (d.toBitVec.getLsbD 3)
          (c.toBitVec.getLsbD 29) (d.toBitVec.getLsbD 9) (c.toBitVec.getLsbD 31) (d.toBitVec.getLsbD 10)
          (d.toBitVec.getLsbD 11) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 57 =
      lifeB (d.toBitVec.getLsbD 9) (d.toBitVec.getLsbD 2) (d.toBitVec.getLsbD 3) (d.toBitVec.getLsbD 6)
          (d.toBitVec.getLsbD 8) (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 10) (d.toBitVec.getLsbD 11)
          (d.toBitVec.getLsbD 14) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 60 =
      lifeB (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 3) (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 7)
          (d.toBitVec.getLsbD 9) (d.toBitVec.getLsbD 13) (d.toBitVec.getLsbD 11) (d.toBitVec.getLsbD 14)
          (d.toBitVec.getLsbD 15) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 61 =
      lifeB (d.toBitVec.getLsbD 13) (d.toBitVec.getLsbD 6) (d.toBitVec.getLsbD 7) (d.toBitVec.getLsbD 18)
          (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 24) (d.toBitVec.getLsbD 14) (d.toBitVec.getLsbD 15)
          (d.toBitVec.getLsbD 26) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 42 =
      lifeB (c.toBitVec.getLsbD 26) (c.toBitVec.getLsbD 13) (c.toBitVec.getLsbD 24) (c.toBitVec.getLsbD 25)
          (c.toBitVec.getLsbD 15) (c.toBitVec.getLsbD 27) (c.toBitVec.getLsbD 37) (c.toBitVec.getLsbD 48)
          (c.toBitVec.getLsbD 49) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 43 =
      lifeB (c.toBitVec.getLsbD 27) (c.toBitVec.getLsbD 24) (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 28)
          (c.toBitVec.getLsbD 26) (c.toBitVec.getLsbD 30) (c.toBitVec.getLsbD 48) (c.toBitVec.getLsbD 49)
          (c.toBitVec.getLsbD 52) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 46 =
      lifeB (c.toBitVec.getLsbD 30) (c.toBitVec.getLsbD 25) (c.toBitVec.getLsbD 28) (c.toBitVec.getLsbD 29)
          (c.toBitVec.getLsbD 27) (c.toBitVec.getLsbD 31) (c.toBitVec.getLsbD 49) (c.toBitVec.getLsbD 52)
          (c.toBitVec.getLsbD 53) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 47 =
      lifeB (c.toBitVec.getLsbD 31) (c.toBitVec.getLsbD 28) (c.toBitVec.getLsbD 29) (d.toBitVec.getLsbD 8)
          (c.toBitVec.getLsbD 30) (d.toBitVec.getLsbD 10) (c.toBitVec.getLsbD 52) (c.toBitVec.getLsbD 53)
          (d.toBitVec.getLsbD 32) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 58 =
      lifeB (d.toBitVec.getLsbD 10) (c.toBitVec.getLsbD 29) (d.toBitVec.getLsbD 8) (d.toBitVec.getLsbD 9)
          (c.toBitVec.getLsbD 31) (d.toBitVec.getLsbD 11) (c.toBitVec.getLsbD 53) (d.toBitVec.getLsbD 32)
          (d.toBitVec.getLsbD 33) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 59 =
      lifeB (d.toBitVec.getLsbD 11) (d.toBitVec.getLsbD 8) (d.toBitVec.getLsbD 9) (d.toBitVec.getLsbD 12)
          (d.toBitVec.getLsbD 10) (d.toBitVec.getLsbD 14) (d.toBitVec.getLsbD 32) (d.toBitVec.getLsbD 33)
          (d.toBitVec.getLsbD 36) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 62 =
      lifeB (d.toBitVec.getLsbD 14) (d.toBitVec.getLsbD 9) (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 13)
          (d.toBitVec.getLsbD 11) (d.toBitVec.getLsbD 15) (d.toBitVec.getLsbD 33) (d.toBitVec.getLsbD 36)
          (d.toBitVec.getLsbD 37) ∧
    (computeLevel4NextGen16x16UInt a b c d).toBitVec.getLsbD 63 =
      lifeB (d.toBitVec.getLsbD 15) (d.toBitVec.getLsbD 12) (d.toBitVec.getLsbD 13) (d.toBitVec.getLsbD 24)
          (d.toBitVec.getLsbD 14) (d.toBitVec.getLsbD 26) (d.toBitVec.getLsbD 36) (d.toBitVec.getLsbD 37)
          (d.toBitVec.getLsbD 48) := by
  unfold computeLevel4NextGen16x16UInt computeLevel4NextGen16x16WithUInt computeLeafNextGen8x8BranchUInt
    computeLeafNextGen8x8FastUInt computeNextGen4x4UInt computeNextGen4x4BitwiseUInt bitRuleUInt neighborCount11UInt neighborCount12UInt
    neighborCount21UInt neighborCount22UInt extractCenterUInt extractHorizontalMidUInt extractVerticalMidUInt
    extractCenterMidUInt quad0UInt quad1UInt quad2UInt quad3UInt packLeafFrom4x4sUInt
    centeredSubnodeLevel3BitsUInt centeredHorizontalSubnodeLevel3BitsUInt centeredVerticalSubnodeLevel3BitsUInt
    centeredSubSubnodeLevel4BitsUInt packCentralNibblesUInt lifeB
  bv_decide (config := {timeout := 600})

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/--
Bit-level specification of `centeredSubnodeLevel4`: the output leaf is the central 8x8 of the 16x16
square formed by the four input leaves.
-/
theorem centeredSubnodeLevel4_bits (a b c d : UInt64) :
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 0 = a.toBitVec.getLsbD 48 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 1 = a.toBitVec.getLsbD 49 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 4 = a.toBitVec.getLsbD 52 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 5 = a.toBitVec.getLsbD 53 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 16 = b.toBitVec.getLsbD 32 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 17 = b.toBitVec.getLsbD 33 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 20 = b.toBitVec.getLsbD 36 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 21 = b.toBitVec.getLsbD 37 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 2 = a.toBitVec.getLsbD 50 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 3 = a.toBitVec.getLsbD 51 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 6 = a.toBitVec.getLsbD 54 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 7 = a.toBitVec.getLsbD 55 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 18 = b.toBitVec.getLsbD 34 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 19 = b.toBitVec.getLsbD 35 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 22 = b.toBitVec.getLsbD 38 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 23 = b.toBitVec.getLsbD 39 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 8 = a.toBitVec.getLsbD 56 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 9 = a.toBitVec.getLsbD 57 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 12 = a.toBitVec.getLsbD 60 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 13 = a.toBitVec.getLsbD 61 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 24 = b.toBitVec.getLsbD 40 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 25 = b.toBitVec.getLsbD 41 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 28 = b.toBitVec.getLsbD 44 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 29 = b.toBitVec.getLsbD 45 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 10 = a.toBitVec.getLsbD 58 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 11 = a.toBitVec.getLsbD 59 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 14 = a.toBitVec.getLsbD 62 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 15 = a.toBitVec.getLsbD 63 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 26 = b.toBitVec.getLsbD 42 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 27 = b.toBitVec.getLsbD 43 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 30 = b.toBitVec.getLsbD 46 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 31 = b.toBitVec.getLsbD 47 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 32 = c.toBitVec.getLsbD 16 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 33 = c.toBitVec.getLsbD 17 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 36 = c.toBitVec.getLsbD 20 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 37 = c.toBitVec.getLsbD 21 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 48 = d.toBitVec.getLsbD 0 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 49 = d.toBitVec.getLsbD 1 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 52 = d.toBitVec.getLsbD 4 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 53 = d.toBitVec.getLsbD 5 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 34 = c.toBitVec.getLsbD 18 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 35 = c.toBitVec.getLsbD 19 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 38 = c.toBitVec.getLsbD 22 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 39 = c.toBitVec.getLsbD 23 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 50 = d.toBitVec.getLsbD 2 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 51 = d.toBitVec.getLsbD 3 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 54 = d.toBitVec.getLsbD 6 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 55 = d.toBitVec.getLsbD 7 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 40 = c.toBitVec.getLsbD 24 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 41 = c.toBitVec.getLsbD 25 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 44 = c.toBitVec.getLsbD 28 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 45 = c.toBitVec.getLsbD 29 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 56 = d.toBitVec.getLsbD 8 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 57 = d.toBitVec.getLsbD 9 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 60 = d.toBitVec.getLsbD 12 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 61 = d.toBitVec.getLsbD 13 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 42 = c.toBitVec.getLsbD 26 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 43 = c.toBitVec.getLsbD 27 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 46 = c.toBitVec.getLsbD 30 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 47 = c.toBitVec.getLsbD 31 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 58 = d.toBitVec.getLsbD 10 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 59 = d.toBitVec.getLsbD 11 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 62 = d.toBitVec.getLsbD 14 ∧
    (centeredSubnodeLevel4 a b c d).toBitVec.getLsbD 63 = d.toBitVec.getLsbD 15 := by
  unfold centeredSubnodeLevel4
  bv_decide

set_option linter.unusedSimpArgs false in
theorem leafAt_computeLevel4NextGen16x16UInt (a b c d : UInt64) (x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < 8) (hy0 : 0 ≤ y) (hy : y < 8) :
    leafAt (computeLevel4NextGen16x16UInt a b c d) x y =
    nextGenAt (quadSel (leafAt a) (leafAt b) (leafAt c) (leafAt d) 8) (x + 4) (y + 4) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23,
      k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45,
      k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63⟩ := level4_kernel_bits
          a b c d
  rw [nextGenAt_eq_lifeB]
  have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
  have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;>
    simp only [quadSel, leafAt, mortonIndex, Int.reduceAdd, Int.reduceSub, Int.reduceLT, Int.reduceLE,
      Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte,
      and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21,
        k22, k23,
      k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45,
      k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63]

set_option linter.unusedSimpArgs false in
theorem leafAt_centeredSubnodeLevel4 (a b c d : UInt64) (x y : ℤ)
    (hx0 : 0 ≤ x) (hx : x < 8) (hy0 : 0 ≤ y) (hy : y < 8) :
    leafAt (centeredSubnodeLevel4 a b c d) x y =
    quadSel (leafAt a) (leafAt b) (leafAt c) (leafAt d) 8 (x + 4) (y + 4) := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23,
      k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45,
      k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63⟩ :=
          centeredSubnodeLevel4_bits a b c d
  have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
  have hy' : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 ∨ y = 7 := by omega
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;>
    simp only [quadSel, leafAt, mortonIndex, Int.reduceAdd, Int.reduceSub, Int.reduceLT, Int.reduceLE,
      Int.reduceToNat, Int.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte,
      and_self, true_and, and_true] <;>
    simp only [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21,
        k22, k23,
      k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45,
      k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63]

-- =========================================================================
-- Population Count Facts
-- =========================================================================

theorem popcount64_eq_zero_iff (x : UInt64) : popcount64 x = 0 ↔ x = 0 := by
  unfold popcount64
  constructor <;> intro h <;> bv_decide

theorem popcount64_le (x : UInt64) : popcount64 x ≤ 64 := by
  unfold popcount64
  bv_decide

theorem popcount64_toNat_le (x : UInt64) : (popcount64 x).toNat ≤ 64 := by
  have := popcount64_le x
  rw [UInt32.le_iff_toNat_le] at this
  simpa using this

theorem popcount64_split_se (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0xFFFF000000000000) + popcount64 (a &&& 0x0000FFFFFFFFFFFF) := by
  unfold popcount64
  bv_decide

theorem popcount64_split_sw (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x0000FFFF00000000) + popcount64 (a &&& 0xFFFF0000FFFFFFFF) := by
  unfold popcount64
  bv_decide

theorem popcount64_split_ne (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x00000000FFFF0000) + popcount64 (a &&& 0xFFFFFFFF0000FFFF) := by
  unfold popcount64
  bv_decide

theorem popcount64_split_nw (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x000000000000FFFF) + popcount64 (a &&& 0xFFFFFFFFFFFF0000) := by
  unfold popcount64
  bv_decide

theorem popcount64_centeredSubnodeLevel4 (a b c d : UInt64) :
    popcount64 (centeredSubnodeLevel4 a b c d) =
    popcount64 (a &&& 0xFFFF000000000000) + popcount64 (b &&& 0x0000FFFF00000000) +
    popcount64 (c &&& 0x00000000FFFF0000) + popcount64 (d &&& 0x000000000000FFFF) := by
  unfold popcount64 centeredSubnodeLevel4
  bv_decide

end Algorithm

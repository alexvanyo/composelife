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
import Algorithm.MacroCell

/-!
# Population count

`popcount64` (inlined into the generated Kotlin wherever a population is needed) is the SWAR population count.
This file proves it equal to the number of set bits, `BitVec.cpop`, which is also what Kotlin's
`ULong.countOneBits()` computes, and derives the facts about masked populations used by the HashLife proofs.
-/

namespace Algorithm

theorem popcount64_eq_zero_iff (x : UInt64) : popcount64 x = 0 ↔ x = 0 := by
  unfold popcount64
  constructor
  · intro h
    bv_check "lrat/PopcountProofs.Algorithm.popcount64_eq_zero_iff-1.lrat"
  · intro h
    bv_check "lrat/PopcountProofs.Algorithm.popcount64_eq_zero_iff-2.lrat"

theorem popcount64_le (x : UInt64) : popcount64 x ≤ 64 := by
  unfold popcount64
  bv_check "lrat/PopcountProofs.Algorithm.popcount64_le.lrat"

theorem popcount64_toNat_le (x : UInt64) : (popcount64 x).toNat ≤ 64 :=
  UInt32.le_iff_toNat_le.mp (popcount64_le x)

theorem popcount64_toNat_eq_cpop (x : UInt64) : (popcount64 x).toNat = x.toBitVec.cpop.toNat := by
  have h : x.toBitVec.cpop = (popcount64 x).toBitVec.setWidth 64 := by
    unfold popcount64
    bv_check "lrat/PopcountProofs.Algorithm.popcount64_toNat_eq_cpop.lrat"
  rw [h, BitVec.toNat_setWidth, UInt32.toNat_toBitVec, Nat.mod_eq_of_lt (by have := popcount64_toNat_le x; omega)]

theorem popcount64_split_se (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0xFFFF000000000000) + popcount64 (a &&& 0x0000FFFFFFFFFFFF) := by
  unfold popcount64
  bv_check "lrat/PopcountProofs.Algorithm.popcount64_split_se.lrat"

theorem popcount64_split_sw (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x0000FFFF00000000) + popcount64 (a &&& 0xFFFF0000FFFFFFFF) := by
  unfold popcount64
  bv_check "lrat/PopcountProofs.Algorithm.popcount64_split_sw.lrat"

theorem popcount64_split_ne (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x00000000FFFF0000) + popcount64 (a &&& 0xFFFFFFFF0000FFFF) := by
  unfold popcount64
  bv_check "lrat/PopcountProofs.Algorithm.popcount64_split_ne.lrat"

theorem popcount64_split_nw (a : UInt64) :
    popcount64 a = popcount64 (a &&& 0x000000000000FFFF) + popcount64 (a &&& 0xFFFFFFFFFFFF0000) := by
  unfold popcount64
  bv_check "lrat/PopcountProofs.Algorithm.popcount64_split_nw.lrat"

/-- A word that has a bit in common with a mask is nonzero after masking. -/
theorem UInt64.and_ne_zero_of_getLsbD {l m : UInt64} {k : Nat} (hl : l.toBitVec.getLsbD k = true)
    (hm : m.toBitVec.getLsbD k = true) : l &&& m ≠ 0 := by
  intro h
  have := congrArg (fun v : UInt64 => v.toBitVec.getLsbD k) h
  simp [hl, hm] at this

end Algorithm

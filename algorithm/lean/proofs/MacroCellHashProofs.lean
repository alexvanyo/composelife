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
import Algorithm.MacroCellHash
import AlgorithmDefs

namespace Algorithm

theorem inv_M_nw_64_valid_Impl : M_nw_64 * inv_M_nw_64 = 1 := by rfl
theorem inv_M_ne_64_valid_Impl : M_ne_64 * inv_M_ne_64 = 1 := by rfl
theorem inv_M_sw_64_valid_Impl : M_sw_64 * inv_M_sw_64 = 1 := by rfl
theorem inv_M_se_64_valid_Impl : M_se_64 * inv_M_se_64 = 1 := by rfl

theorem inv_mix64_1_valid_Impl : mix64_1 * inv_mix64_1 = 1 := by rfl
theorem inv_mix64_2_valid_Impl : mix64_2 * inv_mix64_2 = 1 := by rfl

theorem inv_C_lvl_32_valid_Impl : C_lvl_32 * inv_C_lvl_32 = 1 := by rfl
theorem inv_C_nw_32_valid_Impl  : C_nw_32  * inv_C_nw_32  = 1 := by rfl
theorem inv_C_ne_32_valid_Impl  : C_ne_32  * inv_C_ne_32  = 1 := by rfl
theorem inv_C_sw_32_valid_Impl  : C_sw_32  * inv_C_sw_32  = 1 := by rfl
theorem inv_C_se_32_valid_Impl  : C_se_32  * inv_C_se_32  = 1 := by rfl

theorem inv_mix32_1_valid_Impl  : mix32_1  * inv_mix32_1  = 1 := by rfl
theorem inv_mix32_2_valid_Impl  : mix32_2  * inv_mix32_2  = 1 := by rfl

theorem empty_node_hashes_all_distinct_Impl :
    (deduplicate emptyNodeHashesList).length = 27 := by
  rfl

-- =========================================================================
-- Invertibility of the Finalizers
-- =========================================================================

theorem unxorshift64_31 (h : UInt64) :
    let y := h ^^^ (h >>> 31)
    let z := y ^^^ (y >>> 31)
    z ^^^ (z >>> 62) = h := by
  simp only
  bv_check "lrat/MacroCellHashProofs.Algorithm.unxorshift64_31.lrat"

theorem unxorshift64_27 (h : UInt64) :
    let y := h ^^^ (h >>> 27)
    let z := y ^^^ (y >>> 27)
    z ^^^ (z >>> 54) = h := by
  simp only
  bv_check "lrat/MacroCellHashProofs.Algorithm.unxorshift64_27.lrat"

theorem unxorshift64_30 (h : UInt64) :
    let y := h ^^^ (h >>> 30)
    let z := y ^^^ (y >>> 30)
    z ^^^ (z >>> 60) = h := by
  simp only
  bv_check "lrat/MacroCellHashProofs.Algorithm.unxorshift64_30.lrat"

theorem unxorshift32_13 (h : UInt32) :
    let y := h ^^^ (h >>> 13)
    let z := y ^^^ (y >>> 13)
    z ^^^ (z >>> 26) = h := by
  simp only
  bv_check "lrat/MacroCellHashProofs.Algorithm.unxorshift32_13.lrat"

theorem unxorshift32_16 (h : UInt32) : (h ^^^ (h >>> 16)) ^^^ ((h ^^^ (h >>> 16)) >>> 16) = h := by
  bv_check "lrat/MacroCellHashProofs.Algorithm.unxorshift32_16.lrat"

theorem mul_inv_cancel64 {a m minv : UInt64} (h : m * minv = 1) : a * m * minv = a := by
  rw [UInt64.mul_assoc, h, UInt64.mul_one]

theorem mul_inv_cancel32 {a m minv : UInt32} (h : m * minv = 1) : a * m * minv = a := by
  rw [UInt32.mul_assoc, h, UInt32.mul_one]

/-- `unmix13` inverts the Mix13 finalizer of `level4Hash`, so `mix13` is a bijection of `UInt64`. -/
theorem unmix13_mix13 (x : UInt64) : unmix13 (mix13 x) = x := by
  unfold unmix13 mix13
  simp only
  rw [unxorshift64_31, mul_inv_cancel64 inv_mix64_2_valid_Impl, unxorshift64_27,
    mul_inv_cancel64 inv_mix64_1_valid_Impl, unxorshift64_30]

/-- `unfmix32` inverts the fmix32 finalizer of `cellNodeHash`, so `fmix32` is a bijection of `UInt32`. -/
theorem unfmix32_fmix32 (x : UInt32) : unfmix32 (fmix32 x) = x := by
  unfold unfmix32 fmix32
  simp only
  rw [unxorshift32_16, mul_inv_cancel32 inv_mix32_2_valid_Impl, unxorshift32_13,
    mul_inv_cancel32 inv_mix32_1_valid_Impl, unxorshift32_16]

end Algorithm

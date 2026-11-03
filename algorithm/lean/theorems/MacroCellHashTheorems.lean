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

import Algorithm.Basic
import Algorithm.MacroCellHash
import AlgorithmDefs
import proofs.MacroCellHashProofs

namespace Algorithm

theorem inv_M_nw_64_valid : M_nw_64 * inv_M_nw_64 = 1 :=
  inv_M_nw_64_valid_Impl

theorem inv_M_ne_64_valid : M_ne_64 * inv_M_ne_64 = 1 :=
  inv_M_ne_64_valid_Impl

theorem inv_M_sw_64_valid : M_sw_64 * inv_M_sw_64 = 1 :=
  inv_M_sw_64_valid_Impl

theorem inv_M_se_64_valid : M_se_64 * inv_M_se_64 = 1 :=
  inv_M_se_64_valid_Impl

theorem inv_mix64_1_valid : mix64_1 * inv_mix64_1 = 1 :=
  inv_mix64_1_valid_Impl

theorem inv_mix64_2_valid : mix64_2 * inv_mix64_2 = 1 :=
  inv_mix64_2_valid_Impl

theorem inv_C_lvl_32_valid : C_lvl_32 * inv_C_lvl_32 = 1 :=
  inv_C_lvl_32_valid_Impl

theorem inv_C_nw_32_valid : C_nw_32 * inv_C_nw_32 = 1 :=
  inv_C_nw_32_valid_Impl

theorem inv_C_ne_32_valid : C_ne_32 * inv_C_ne_32 = 1 :=
  inv_C_ne_32_valid_Impl

theorem inv_C_sw_32_valid : C_sw_32 * inv_C_sw_32 = 1 :=
  inv_C_sw_32_valid_Impl

theorem inv_C_se_32_valid : C_se_32 * inv_C_se_32 = 1 :=
  inv_C_se_32_valid_Impl

theorem inv_mix32_1_valid : mix32_1 * inv_mix32_1 = 1 :=
  inv_mix32_1_valid_Impl

theorem inv_mix32_2_valid : mix32_2 * inv_mix32_2 = 1 :=
  inv_mix32_2_valid_Impl

/-- `mix13` (the finalizer of `level4Hash`) is a bijection: `unmix13` inverts it. -/
theorem mix13_invertible (x : UInt64) : unmix13 (mix13 x) = x :=
  unmix13_mix13 x

/-- `fmix32` (the finalizer of `cellNodeHash`) is a bijection: `unfmix32` inverts it. -/
theorem fmix32_invertible (x : UInt32) : unfmix32 (fmix32 x) = x :=
  unfmix32_fmix32 x

/-- The pre-built empty nodes of levels 4 to 30 have distinct hashes. -/
theorem empty_node_hashes_all_distinct :
    (deduplicate emptyNodeHashesList).length = 27 :=
  empty_node_hashes_all_distinct_Impl

end Algorithm

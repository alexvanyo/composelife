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

theorem mix13_invertible_zero : unmix13 (mix13 0) = 0 :=
  mix13_invertible_zero_Impl

theorem mix13_invertible_one : unmix13 (mix13 1) = 1 :=
  mix13_invertible_one_Impl

theorem mix13_invertible_max : unmix13 (mix13 0xFFFFFFFFFFFFFFFF) = 0xFFFFFFFFFFFFFFFF :=
  mix13_invertible_max_Impl

theorem mix13_invertible_alt1 : unmix13 (mix13 0x5555555555555555) = 0x5555555555555555 :=
  mix13_invertible_alt1_Impl

theorem mix13_invertible_alt2 : unmix13 (mix13 0xAAAAAAAAAAAAAAAA) = 0xAAAAAAAAAAAAAAAA :=
  mix13_invertible_alt2_Impl

theorem mix13_invertible_sample : unmix13 (mix13 0x123456789ABCDEF0) = 0x123456789ABCDEF0 :=
  mix13_invertible_sample_Impl

theorem fmix32_invertible_zero : unfmix32 (fmix32 0) = 0 :=
  fmix32_invertible_zero_Impl

theorem fmix32_invertible_one : unfmix32 (fmix32 1) = 1 :=
  fmix32_invertible_one_Impl

theorem fmix32_invertible_max : unfmix32 (fmix32 0xFFFFFFFF) = 0xFFFFFFFF :=
  fmix32_invertible_max_Impl

theorem fmix32_invertible_alt1 : unfmix32 (fmix32 0x55555555) = 0x55555555 :=
  fmix32_invertible_alt1_Impl

theorem fmix32_invertible_alt2 : unfmix32 (fmix32 0xAAAAAAAA) = 0xAAAAAAAA :=
  fmix32_invertible_alt2_Impl

theorem fmix32_invertible_sample : unfmix32 (fmix32 0x12345678) = 0x12345678 :=
  fmix32_invertible_sample_Impl

theorem legacy_symmetric_leaf_collides_with_zero :
    let northHalf : UInt64 := 0x12345678
    let symmetricLeaf : UInt64 := northHalf ||| (northHalf <<< 32)
    legacyLevel4Hash symmetricLeaf 0 0 0 = legacyLevel4Hash 0 0 0 0 :=
  legacy_symmetric_leaf_collides_with_zero_Impl

theorem new_symmetric_leaf_does_not_collide :
    let northHalf : UInt64 := 0x12345678
    let symmetricLeaf : UInt64 := northHalf ||| (northHalf <<< 32)
    (level4Hash symmetricLeaf 0 0 0 == level4Hash 0 0 0 0) = false :=
  new_symmetric_leaf_does_not_collide_Impl

theorem level4_quadrant_permutations_distinct :
    let a : UInt64 := 0x0123456789ABCDEF
    let b : UInt64 := 0xFEDCBA9876543210
    let c : UInt64 := 0x5555AAAA5555AAAA
    let d : UInt64 := 0x3333CCCC3333CCCC
    let h1 := level4Hash a b c d
    let h2 := level4Hash b a c d
    let h3 := level4Hash a c b d
    let h4 := level4Hash d c b a
    (h1 != h2 && h1 != h3 && h1 != h4 && h2 != h3 && h2 != h4 && h3 != h4) = true :=
  level4_quadrant_permutations_distinct_Impl

theorem cellnode_quadrant_permutations_distinct :
    let a : UInt32 := 0x11111111
    let b : UInt32 := 0x22222222
    let c : UInt32 := 0x44444444
    let d : UInt32 := 0x88888888
    let h1 := cellNodeHash 5 a b c d
    let h2 := cellNodeHash 5 b a c d
    let h3 := cellNodeHash 5 a c b d
    let h4 := cellNodeHash 5 d c b a
    (h1 != h2 && h1 != h3 && h1 != h4 && h2 != h3 && h2 != h4 && h3 != h4) = true :=
  cellnode_quadrant_permutations_distinct_Impl

theorem empty_node_hashes_all_distinct :
    (deduplicate emptyNodeHashesList).length = 27 :=
  empty_node_hashes_all_distinct_Impl

end Algorithm

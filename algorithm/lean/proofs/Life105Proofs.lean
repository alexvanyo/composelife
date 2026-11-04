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

import Algorithm.Life105

namespace Algorithm

theorem deserializeLife105_empty_Impl :
    deserializeLife105 #[] = ⟨0, "", 0, 0, #[⟨0, "", 0, 0⟩], #[]⟩ := by
  unfold deserializeLife105
  rfl

theorem deserializeLife105_empty_pattern_Impl :
    deserializeLife105 #["#Life 1.05", "#N"] = ⟨0, "", 0, 0, #[], #[]⟩ := by
  decide +kernel

theorem deserializeLife105_invalid_header_Impl (hdr : String) (h : hdr ≠ "#Life 1.05") :
    deserializeLife105 #[hdr] = ⟨1, hdr, 1, 0, #[], #[]⟩ := by
  unfold deserializeLife105
  have h_diff : (hdr != "#Life 1.05") = true := by
    rw [bne_iff_ne]
    exact h
  simp [h_diff]

theorem serializeLife105Block_empty_Impl :
    serializeLife105Block #[] 0 0 0 =
    #["................................................................................"] := by
  decide +kernel

theorem checkRuleLine_conway_Impl :
    checkRuleLine "#R 23/3".toByteArray = 0 := by
  decide +kernel

theorem checkRuleLine_unsupported_Impl :
    checkRuleLine "#R 23/4".toByteArray = 2 := by
  decide +kernel

theorem checkRuleLine_malformed_Impl :
    checkRuleLine "#R invalid".toByteArray = 1 := by
  decide +kernel

theorem parseBlockHeader_valid_Impl :
    parseBlockHeader "#P 0 0".toByteArray = some ⟨0, 0⟩ := by
  decide +kernel

theorem parseBlockHeader_negative_Impl :
    parseBlockHeader "#P -10 25".toByteArray = some ⟨-10, 25⟩ := by
  decide +kernel

theorem isRowLine_valid_Impl :
    isRowLine "*.*.*".toByteArray = true := by
  decide +kernel

theorem isRowLine_invalid_Impl :
    isRowLine "*.*X*".toByteArray = false := by
  decide +kernel

theorem deserializeLife105_single_cell_Impl :
    deserializeLife105 #["#Life 1.05", "#N", "#P 0 0", "*"] =
    ⟨0, "", 0, 0, #[], #[(0, 0)]⟩ := by
  decide +kernel

theorem life105_block_roundtrip_single_Impl :
    deserializeLife105 (#["#Life 1.05", "#N", "#P 0 0"] ++ serializeLife105Block #[(0, 0)] 0 0 0) =
    ⟨0, "", 0, 0, #[], #[(0, 0)]⟩ := by
  decide +kernel

theorem life105_block_roundtrip_block_Impl :
    deserializeLife105
      (#["#Life 1.05", "#N", "#P 0 0"] ++
        serializeLife105Block #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 0 1) =
    ⟨0, "", 0, 0, #[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ := by
  decide +kernel

theorem life105_block_roundtrip_blinker_Impl :
    deserializeLife105
      (#["#Life 1.05", "#N", "#P 0 0"] ++
        serializeLife105Block #[(0, 0), (1, 0), (2, 0)] 0 0 0) =
    ⟨0, "", 0, 0, #[], #[(0, 0), (1, 0), (2, 0)]⟩ := by
  decide +kernel

end Algorithm

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

import Algorithm.RLE

namespace Algorithm

theorem rleCombine_empty_Impl :
    rleCombine #[] = #[] := by
  unfold rleCombine
  rfl

theorem rleCombine_combine_Impl :
    rleCombine #[(111, 2), (111, 3)] = #[(111, 5)] := by
  decide +kernel

theorem rleCombine_distinct_Impl :
    rleCombine #[(111, 1), (98, 1)] = #[(111, 1), (98, 1)] := by
  decide +kernel

theorem serializeRLE_empty_Impl :
    serializeRLE #[] 0 0 0 0 = #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"] := by
  unfold serializeRLE
  rfl

theorem serializeRLE_single_Impl :
    serializeRLE #[(0, 0)] 0 0 0 0 = #["#R 0 0", "x = 1, y = 1, rule = B3/S23", "o!"] := by
  decide +kernel

theorem decodeRLERuns_single_alive_Impl :
    decodeRLERuns #[(2, 1)] 0 0 = #[(0, 0)] := by
  decide +kernel

theorem decodeRLERuns_empty_Impl (x y : Int32) :
    decodeRLERuns #[] x y = #[] := by
  simp [decodeRLERuns, decodeRLERuns.loop]

theorem rleCombine_single_run_Impl (tag : UInt8) (count : UInt32) :
    rleCombine #[(tag, count)] = #[(tag, count)] := by
  unfold rleCombine
  dsimp
  unfold rleCombine.loop
  rfl

theorem rleCombine_idempotent_single_run_Impl (tag : UInt8) (count : UInt32) :
    rleCombine (rleCombine #[(tag, count)]) = rleCombine #[(tag, count)] := by
  simp only [rleCombine_single_run_Impl]

theorem rleCombine_triple_same_Impl (tag : UInt8) :
    rleCombine #[(tag, 1), (tag, 2), (tag, 3)] = #[(tag, 6)] := by
  decide +kernel +revert

theorem decodeRLERuns_two_cells_Impl :
    decodeRLERuns #[(2, 2)] 5 10 = #[(5, 10), (6, 10)] := by
  decide +kernel

theorem decodeRLERuns_row_advance_Impl :
    decodeRLERuns #[(2, 1), (0, 1), (2, 1)] 0 0 = #[(0, 0), (0, 1)] := by
  decide +kernel

theorem serializeRLE_blinker_Impl :
    serializeRLE #[(-1, 0), (0, 0), (1, 0)] (-1) 1 0 0 =
    #["#R -1 0", "x = 3, y = 1, rule = B3/S23", "3o!"] := by
  decide +kernel

theorem deserializeRLE_empty_Impl :
    deserializeRLE #[] = ⟨1, "", 0, #[⟨0, 0, 0, 0, "", zeroOffset, zeroOffset⟩], #[]⟩ := by
  unfold deserializeRLE
  rfl

theorem parseRLEHeader_valid_Impl :
    parseRLEHeader "x = 3, y = 1, rule = B3/S23".toByteArray = 0 := by
  decide +kernel

theorem parseRLEHeader_unsupported_rule_Impl :
    parseRLEHeader "x = 3, y = 1, rule = B3/S24".toByteArray = 3 := by
  decide +kernel

theorem parseRLEHeader_invalid_Impl :
    parseRLEHeader "invalid".toByteArray = 2 := by
  decide +kernel

theorem deserializeRLE_single_alive_Impl :
    deserializeRLE #["x = 1, y = 1, rule = B3/S23", "o!"] =
    ⟨0, "", 0, #[], #[(0, 0)]⟩ := by
  decide +kernel

theorem deserializeRLE_offset_single_alive_Impl :
    deserializeRLE #["#R 10 20", "x = 1, y = 1, rule = B3/S23", "o!"] =
    ⟨0, "", 0, #[], #[(10, 20)]⟩ := by
  decide +kernel

theorem rle_roundtrip_empty_Impl :
    deserializeRLE (serializeRLE #[] 0 0 0 0) =
    ⟨0, "", 0, #[], #[]⟩ := by
  decide +kernel

theorem rle_roundtrip_single_Impl :
    deserializeRLE (serializeRLE #[(0, 0)] 0 0 0 0) =
    ⟨0, "", 0, #[], #[(0, 0)]⟩ := by
  decide +kernel

theorem rle_roundtrip_blinker_Impl :
    deserializeRLE (serializeRLE #[(-1, 0), (0, 0), (1, 0)] (-1) 1 0 0) =
    ⟨0, "", 0, #[], #[(-1, 0), (0, 0), (1, 0)]⟩ := by
  decide +kernel

theorem rle_roundtrip_block_Impl :
    deserializeRLE (serializeRLE #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 1 0 1) =
    ⟨0, "", 0, #[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ := by
  decide +kernel

theorem rle_roundtrip_glider_Impl :
    deserializeRLE (serializeRLE #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
    ⟨0, "", 0, #[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ := by
  decide +kernel

end Algorithm

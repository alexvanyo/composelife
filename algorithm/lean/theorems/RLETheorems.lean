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
import proofs.RLEProofs

namespace Algorithm

/-!
# Run-Length Encoding (RLE) Master Theorems

Public specification theorems guaranteeing correct run-length encoding compression,
line wrapping, and serialization for the RLE format.
-/

/-- An empty run sequence produces an empty combined run array. -/
theorem rleCombine_empty :
    rleCombine #[] = #[] :=
  rleCombine_empty_Impl

/-- Consecutive runs with the same character are combined into their sum. -/
theorem rleCombine_combine :
    rleCombine #[(111, 2), (111, 3)] = #[(111, 5)] :=
  rleCombine_combine_Impl

/-- Consecutive runs with distinct characters are preserved. -/
theorem rleCombine_distinct :
    rleCombine #[(111, 1), (98, 1)] = #[(111, 1), (98, 1)] :=
  rleCombine_distinct_Impl

/-- Serializing empty cell state produces the 0x0 header and terminating '!'. -/
theorem serializeRLE_empty :
    serializeRLE #[] 0 0 0 0 = #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"] :=
  serializeRLE_empty_Impl

/-- Serializing a single alive cell produces the 1x1 header and 'o!'. -/
theorem serializeRLE_single :
    serializeRLE #[(0, 0)] 0 0 0 0 = #["#R 0 0", "x = 1, y = 1, rule = B3/S23", "o!"] :=
  serializeRLE_single_Impl

/-- Decoding a single alive run of count 1 at (0, 0) yields [(0, 0)]. -/
theorem decodeRLERuns_single_alive :
    decodeRLERuns #[(2, 1)] 0 0 = #[(0, 0)] :=
  decodeRLERuns_single_alive_Impl

/-- Decoding empty run sequence produces empty coordinates. -/
theorem decodeRLERuns_empty (x y : Int32) :
    decodeRLERuns #[] x y = #[] :=
  decodeRLERuns_empty_Impl x y

/-- Combining a single run is the identity for any tag and count. -/
theorem rleCombine_single_run (tag : UInt8) (count : UInt32) :
    rleCombine #[(tag, count)] = #[(tag, count)] :=
  rleCombine_single_run_Impl tag count

/-- Combining a single run is idempotent for any tag and count. -/
theorem rleCombine_idempotent_single_run (tag : UInt8) (count : UInt32) :
    rleCombine (rleCombine #[(tag, count)]) = rleCombine #[(tag, count)] :=
  rleCombine_idempotent_single_run_Impl tag count

/-- Combining three identical consecutive runs sums their lengths. -/
theorem rleCombine_triple_same (tag : UInt8) :
    rleCombine #[(tag, 1), (tag, 2), (tag, 3)] = #[(tag, 6)] :=
  rleCombine_triple_same_Impl tag

/-- Decoding an alive run of count 2 at (5, 10) yields coordinates [(5, 10), (6, 10)]. -/
theorem decodeRLERuns_two_cells :
    decodeRLERuns #[(2, 2)] 5 10 = #[(5, 10), (6, 10)] :=
  decodeRLERuns_two_cells_Impl

/-- Decoding alive runs separated by row advance (0, 1) yields vertically displaced cells. -/
theorem decodeRLERuns_row_advance :
    decodeRLERuns #[(2, 1), (0, 1), (2, 1)] 0 0 = #[(0, 0), (0, 1)] :=
  decodeRLERuns_row_advance_Impl

/-- Serializing a 3-cell blinker pattern produces header with '3o!' compression. -/
theorem serializeRLE_blinker :
    serializeRLE #[(-1, 0), (0, 0), (1, 0)] (-1) 1 0 0 =
    #["#R -1 0", "x = 3, y = 1, rule = B3/S23", "3o!"] :=
  serializeRLE_blinker_Impl

/-- Deserializing an empty line array produces status 1 (unexpected empty file). -/
theorem deserializeRLE_empty :
    deserializeRLE #[] = ⟨1, "", 0, #[⟨0, 0, 0, 0, "", zeroOffset, zeroOffset⟩], #[]⟩ :=
  deserializeRLE_empty_Impl

/-- Valid standard header with Conway rule B3/S23 is accepted. -/
theorem parseRLEHeader_valid :
    parseRLEHeader "x = 3, y = 1, rule = B3/S23".toByteArray = 0 :=
  parseRLEHeader_valid_Impl

/-- Header with unsupported rule is rejected with status 3. -/
theorem parseRLEHeader_unsupported_rule :
    parseRLEHeader "x = 3, y = 1, rule = B3/S24".toByteArray = 3 :=
  parseRLEHeader_unsupported_rule_Impl

/-- Malformed header is rejected with status 2. -/
theorem parseRLEHeader_invalid :
    parseRLEHeader "invalid".toByteArray = 2 :=
  parseRLEHeader_invalid_Impl

/-- Deserializing a single alive cell without offset defaults to (0, 0). -/
theorem deserializeRLE_single_alive :
    deserializeRLE #["x = 1, y = 1, rule = B3/S23", "o!"] =
    ⟨0, "", 0, #[], #[(0, 0)]⟩ :=
  deserializeRLE_single_alive_Impl

/-- Deserializing a single alive cell with #R offset sets cell coordinate. -/
theorem deserializeRLE_offset_single_alive :
    deserializeRLE #["#R 10 20", "x = 1, y = 1, rule = B3/S23", "o!"] =
    ⟨0, "", 0, #[], #[(10, 20)]⟩ :=
  deserializeRLE_offset_single_alive_Impl

/-- Roundtrip: empty cell pattern serialized to RLE and deserialized produces 0 cells. -/
theorem rle_roundtrip_empty :
    deserializeRLE (serializeRLE #[] 0 0 0 0) =
    ⟨0, "", 0, #[], #[]⟩ :=
  rle_roundtrip_empty_Impl

/-- Roundtrip: single cell serialized to RLE and deserialized preserves (0, 0). -/
theorem rle_roundtrip_single :
    deserializeRLE (serializeRLE #[(0, 0)] 0 0 0 0) =
    ⟨0, "", 0, #[], #[(0, 0)]⟩ :=
  rle_roundtrip_single_Impl

/-- Roundtrip: 3-cell blinker serialized to RLE and deserialized preserves all coordinates. -/
theorem rle_roundtrip_blinker :
    deserializeRLE (serializeRLE #[(-1, 0), (0, 0), (1, 0)] (-1) 1 0 0) =
    ⟨0, "", 0, #[], #[(-1, 0), (0, 0), (1, 0)]⟩ :=
  rle_roundtrip_blinker_Impl

/-- Roundtrip: 4-cell block serialized to RLE and deserialized preserves all coordinates. -/
theorem rle_roundtrip_block :
    deserializeRLE (serializeRLE #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 1 0 1) =
    ⟨0, "", 0, #[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ :=
  rle_roundtrip_block_Impl

/-- Roundtrip: 5-cell glider serialized to RLE and deserialized preserves all coordinates. -/
theorem rle_roundtrip_glider :
    deserializeRLE (serializeRLE #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
    ⟨0, "", 0, #[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ :=
  rle_roundtrip_glider_Impl

end Algorithm

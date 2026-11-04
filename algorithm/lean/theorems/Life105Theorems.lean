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
import proofs.Life105Proofs

namespace Algorithm

/-!
# Life 1.05 Master Theorems

Public specification theorems guaranteeing correct parsing, error detection, and serialization
for the Life 1.05 format.
-/

/-- An empty line sequence produces the empty file warning and 0 cells. -/
theorem deserializeLife105_empty :
    deserializeLife105 #[] = ⟨0, "", 0, 0, #[⟨0, "", 0, 0⟩], #[]⟩ :=
  deserializeLife105_empty_Impl

/-- An empty pattern with '#Life 1.05' and '#N' succeeds with 0 cells and no warnings. -/
theorem deserializeLife105_empty_pattern :
    deserializeLife105 #["#Life 1.05", "#N"] = ⟨0, "", 0, 0, #[], #[]⟩ :=
  deserializeLife105_empty_pattern_Impl

/-- A line sequence whose header is not '#Life 1.05' produces the invalid header status. -/
theorem deserializeLife105_invalid_header (hdr : String) (h : hdr ≠ "#Life 1.05") :
    deserializeLife105 #[hdr] = ⟨1, hdr, 1, 0, #[], #[]⟩ :=
  deserializeLife105_invalid_header_Impl hdr h

/-- Serializing an empty single row block produces 80 '.' characters. -/
theorem serializeLife105Block_empty :
    serializeLife105Block #[] 0 0 0 =
    #["................................................................................"] :=
  serializeLife105Block_empty_Impl

/-- Conway's life rule #R 23/3 is recognized as supported (code 0). -/
theorem checkRuleLine_conway :
    checkRuleLine "#R 23/3".toByteArray = 0 :=
  checkRuleLine_conway_Impl

/-- Non-standard rule #R 23/4 is recognized as unsupported rule (code 2). -/
theorem checkRuleLine_unsupported :
    checkRuleLine "#R 23/4".toByteArray = 2 :=
  checkRuleLine_unsupported_Impl

/-- Malformed rule #R invalid is recognized as malformed input (code 1). -/
theorem checkRuleLine_malformed :
    checkRuleLine "#R invalid".toByteArray = 1 :=
  checkRuleLine_malformed_Impl

/-- Parsing a valid '#P 0 0' block header correctly extracts (0, 0). -/
theorem parseBlockHeader_valid :
    parseBlockHeader "#P 0 0".toByteArray = some ⟨0, 0⟩ :=
  parseBlockHeader_valid_Impl

/-- Parsing signed block headers '#P -10 25' correctly extracts (-10, 25). -/
theorem parseBlockHeader_negative :
    parseBlockHeader "#P -10 25".toByteArray = some ⟨-10, 25⟩ :=
  parseBlockHeader_negative_Impl

/-- Valid row containing only '.' and '*' is recognized. -/
theorem isRowLine_valid :
    isRowLine "*.*.*".toByteArray = true :=
  isRowLine_valid_Impl

/-- Row containing invalid characters is rejected. -/
theorem isRowLine_invalid :
    isRowLine "*.*X*".toByteArray = false :=
  isRowLine_invalid_Impl

/-- Deserializing a single cell pattern succeeds. -/
theorem deserializeLife105_single_cell :
    deserializeLife105 #["#Life 1.05", "#N", "#P 0 0", "*"] =
    ⟨0, "", 0, 0, #[], #[(0, 0)]⟩ :=
  deserializeLife105_single_cell_Impl

/-- Roundtrip: serializing a single cell and deserializing it preserves the cell coordinate. -/
theorem life105_block_roundtrip_single :
    deserializeLife105 (#["#Life 1.05", "#N", "#P 0 0"] ++ serializeLife105Block #[(0, 0)] 0 0 0) =
    ⟨0, "", 0, 0, #[], #[(0, 0)]⟩ :=
  life105_block_roundtrip_single_Impl

/-- Roundtrip: serializing a 2x2 block and deserializing it recovers all 4 cell coordinates. -/
theorem life105_block_roundtrip_block :
    deserializeLife105
      (#["#Life 1.05", "#N", "#P 0 0"] ++
        serializeLife105Block #[(0, 0), (1, 0), (0, 1), (1, 1)] 0 0 1) =
    ⟨0, "", 0, 0, #[], #[(0, 0), (1, 0), (0, 1), (1, 1)]⟩ :=
  life105_block_roundtrip_block_Impl

/-- Roundtrip: serializing a blinker and deserializing it recovers all 3 cell coordinates. -/
theorem life105_block_roundtrip_blinker :
    deserializeLife105
      (#["#Life 1.05", "#N", "#P 0 0"] ++
        serializeLife105Block #[(0, 0), (1, 0), (2, 0)] 0 0 0) =
    ⟨0, "", 0, 0, #[], #[(0, 0), (1, 0), (2, 0)]⟩ :=
  life105_block_roundtrip_blinker_Impl

end Algorithm

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

import Algorithm.Life106
import proofs.Life106Proofs

namespace Algorithm

/-!
# Life 1.06 Master Theorems

Public specification theorems guaranteeing correct parsing, error detection, and serialization
for the Life 1.06 format.
-/

/-- An empty line sequence produces the emptyFile result status. -/
theorem deserializeLife106_empty :
    deserializeLife106 #[] = ⟨1, 0, "", #[]⟩ :=
  deserializeLife106_empty_Impl

/-- A line sequence whose header is not '#Life 1.06' produces the invalidHeader result status. -/
theorem deserializeLife106_invalid_header (hdr : String) (h : hdr ≠ "#Life 1.06") :
    deserializeLife106 #[hdr] = ⟨2, 1, hdr, #[]⟩ :=
  deserializeLife106_invalid_header_Impl hdr h

/-- Serializing the empty coordinate set produces exactly the header line. -/
theorem serializeLife106_empty :
    serializeLife106 #[] = #["#Life 1.06"] :=
  serializeLife106_empty_Impl

/-- Serializing and deserializing the empty coordinate set round-trips to success. -/
theorem deserializeLife106_round_trip_empty :
    deserializeLife106 (serializeLife106 #[]) = ⟨0, 0, "", #[]⟩ :=
  deserializeLife106_round_trip_empty_Impl

/-- Any input line that cannot be parsed as a coordinate pair produces the invalidLine status at line 2. -/
theorem deserializeLife106_invalid_line (badLine : String) (h : parseCoordLine badLine = none) :
    deserializeLife106 #["#Life 1.06", badLine] = ⟨3, 2, badLine, #[]⟩ :=
  deserializeLife106_invalid_line_Impl badLine h

/-- A single valid coordinate serialized in Life 1.06 produces header plus coordinate line. -/
theorem serializeLife106_single (c : Int32 × Int32) :
    serializeLife106 #[c] = #["#Life 1.06", s!"{c.1} {c.2}"] :=
  serializeLife106_single_Impl c

/-- Two valid coordinates serialized in Life 1.06 produce header plus both coordinate lines in order. -/
theorem serializeLife106_double (c1 c2 : Int32 × Int32) :
    serializeLife106 #[c1, c2] = #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"] :=
  serializeLife106_double_Impl c1 c2

/-- Deserializing a valid header with a single coordinate (10, 20) succeeds and recovers the coordinate. -/
theorem deserializeLife106_single_coord :
    deserializeLife106 #["#Life 1.06", "10 20"] = ⟨0, 0, "", #[(10, 20)]⟩ :=
  deserializeLife106_single_coord_Impl

/-- Round-trip theorem for the origin coordinate (0, 0). -/
theorem deserializeLife106_roundtrip_origin :
    deserializeLife106 (serializeLife106 #[(0, 0)]) = ⟨0, 0, "", #[(0, 0)]⟩ :=
  deserializeLife106_roundtrip_origin_Impl

/-- Round-trip theorem for non-trivial negative and positive coordinates. -/
theorem deserializeLife106_roundtrip_sample :
    deserializeLife106 (serializeLife106 #[(-5, 12), (42, -99)]) = ⟨0, 0, "", #[(-5, 12), (42, -99)]⟩ :=
  deserializeLife106_roundtrip_sample_Impl

/-- Serializing 3 valid coordinates in Life 1.06 produces header plus all 3 coordinate lines in order. -/
theorem serializeLife106_triple (c1 c2 c3 : Int32 × Int32) :
    serializeLife106 #[c1, c2, c3] = #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"] :=
  serializeLife106_triple_Impl c1 c2 c3

/-- Universal round-trip for any coordinate array whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_universal (cells : Array (Int32 × Int32))
    (h_valid : ValidLife106Coords cells) :
    deserializeLife106 (serializeLife106 cells) = ⟨0, 0, "", cells⟩ :=
  deserializeLife106_roundtrip_universal_Impl cells h_valid

/-- Universal round-trip for any single coordinate whose string representation inverts under parseCoordLine. -/
theorem deserializeLife106_roundtrip_single_arbitrary (c : Int32 × Int32)
    (h_parse : parseCoordLine s!"{c.1} {c.2}" = some c) :
    deserializeLife106 (serializeLife106 #[c]) = ⟨0, 0, "", #[c]⟩ :=
  deserializeLife106_roundtrip_single_arbitrary_Impl c h_parse

/-- Universal round-trip for any two coordinates whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_double_arbitrary (c1 c2 : Int32 × Int32)
    (h_parse1 : parseCoordLine s!"{c1.1} {c1.2}" = some c1)
    (h_parse2 : parseCoordLine s!"{c2.1} {c2.2}" = some c2) :
    deserializeLife106 (serializeLife106 #[c1, c2]) = ⟨0, 0, "", #[c1, c2]⟩ :=
  deserializeLife106_roundtrip_double_arbitrary_Impl c1 c2 h_parse1 h_parse2

/-- Universal round-trip for any three coordinates whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_triple_arbitrary (c1 c2 c3 : Int32 × Int32)
    (h_parse1 : parseCoordLine s!"{c1.1} {c1.2}" = some c1)
    (h_parse2 : parseCoordLine s!"{c2.1} {c2.2}" = some c2)
    (h_parse3 : parseCoordLine s!"{c3.1} {c3.2}" = some c3) :
    deserializeLife106 (serializeLife106 #[c1, c2, c3]) = ⟨0, 0, "", #[c1, c2, c3]⟩ :=
  deserializeLife106_roundtrip_triple_arbitrary_Impl c1 c2 c3 h_parse1 h_parse2 h_parse3

/-- For all input line sequences, deserialization returns a status in {0, 1, 2, 3}. -/
theorem deserializeLife106_status_cases (lines : Array String) :
    (deserializeLife106 lines).status = 0 ∨
    (deserializeLife106 lines).status = 1 ∨
    (deserializeLife106 lines).status = 2 ∨
    (deserializeLife106 lines).status = 3 :=
  deserializeLife106_status_cases_Impl lines

/-- The result status of deserializeLife106 is always bounded by 3 for any input. -/
theorem deserializeLife106_status_le_3 (lines : Array String) :
    (deserializeLife106 lines).status ≤ 3 :=
  deserializeLife106_status_le_3_Impl lines

end Algorithm

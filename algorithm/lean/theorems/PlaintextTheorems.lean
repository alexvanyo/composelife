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

import Algorithm.Plaintext
import proofs.PlaintextProofs

namespace Algorithm

/-!
# Plaintext Master Theorems

The round trip for every cell array inside its bounding box, the meaning of any file of pattern rows, and
concrete checks of the warnings.
-/

/-- Deserializing serialized cells gives no warnings and exactly the cells inside the bounding box, moved so the
box starts at the origin. -/
theorem plaintext_round_trip_spec (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) < 2 ^ 31) :
    (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, q ∈ (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).cells ↔
        ∃ c ∈ cells, q = (c.1 - minX, c.2 - minY) :=
  plaintext_round_trip_box cells minX maxX minY maxY hne hcs hbox hsize

/-- Lines of `.` and `O` of one common width deserialize to the `O` positions, row by row, with no warnings. -/
theorem deserializePlaintext_pattern_rows (lines : Array String) (w : Nat) (hl : IsRowLines lines w)
    (hls : lines.size * w < 2 ^ 31) (hne : 1 ≤ lines.size) :
    deserializePlaintext lines = ⟨#[], (linesCells lines 0).toArray⟩ :=
  deserializePlaintext_rows lines w hl hls hne

theorem deserializePlaintext_empty : deserializePlaintext #[] = ⟨#[], #[]⟩ := by
  decide +kernel

theorem deserializePlaintext_comments_ignored :
    deserializePlaintext #["! comment", "O"] = ⟨#[], #[(0, 0)]⟩ := by
  decide +kernel

/-- Serializing no cells gives a single dead cell, which reads back as no cells. -/
theorem plaintext_round_trip_empty :
    deserializePlaintext (serializePlaintext #[] 0 0 0 0) = ⟨#[], #[]⟩ := by
  decide +kernel

theorem plaintext_round_trip_glider :
    deserializePlaintext (serializePlaintext #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
    ⟨#[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ := by
  decide +kernel

/-- Blank lines, short lines and unexpected characters give warnings; unexpected characters other than spaces
are alive. -/
theorem deserializePlaintext_warnings :
    deserializePlaintext #["O.O", "", "O", "x O"] =
      ⟨#[⟨0, 2, 0, 0⟩, ⟨1, 3, 0, 0⟩, ⟨2, 4, 1, 120⟩, ⟨2, 4, 2, 32⟩],
        #[(0, 0), (2, 0), (0, 1), (0, 2), (2, 2)]⟩ := by
  decide +kernel

/-- A non-ASCII character counts as one character: one warning with its code point, and one alive cell. -/
theorem deserializePlaintext_non_ascii :
    deserializePlaintext #["OéO"] = ⟨#[⟨2, 1, 2, 233⟩], #[(0, 0), (1, 0), (2, 0)]⟩ := by
  decide +kernel

end Algorithm

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
import proofs.PlaintextSpecProofs

namespace Algorithm

/-!
# Plaintext Master Theorems

The round trip for every cell array inside its bounding box, the meaning of any file of pattern rows, and
concrete checks of the warnings.
-/

/-- Deserializing serialized cells gives no warnings and exactly the cells inside the bounding box, moved so the
box starts at the origin. -/
theorem plaintext_round_trip_box (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) < 2 ^ 31) :
    (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).cells ↔
        ∃ c ∈ cells, q = (c.1 - minX, c.2 - minY) :=
  plaintext_round_trip_box_Impl cells minX maxX minY maxY hne hcs hbox hsize

/--
Round trip of whole patterns: the serializer computes the bounding box itself, and deserializing gives no warnings
and exactly the cells, moved so that the least x and the least y are 0.
-/
theorem plaintext_round_trip_cells (cells : Array (Int32 × Int32)) (hne : cells.size ≠ 0)
    (hcs : cells.size < 2 ^ 31)
    (hsize : ∀ c ∈ cells, ∀ d ∈ cells, ∀ e ∈ cells, ∀ f ∈ cells,
      (c.1.toInt - d.1.toInt + 1) * (e.2.toInt - f.2.toInt + 1) < 2 ^ 31) :
    let b := cellBox (cells.map cellBits)
    (∀ c ∈ cells, b.1.toInt ≤ c.1.toInt ∧ b.2.2.1.toInt ≤ c.2.toInt) ∧ (∃ c ∈ cells, c.1 = b.1) ∧
      (∃ c ∈ cells, c.2 = b.2.2.1) ∧
      (deserializePlaintext (serializePlaintextCells (cells.map cellBits))).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializePlaintext (serializePlaintextCells (cells.map cellBits))).cells ↔
        ∃ c ∈ cells, q = (c.1 - b.1, c.2 - b.2.2.1) :=
  plaintext_round_trip_cells_Impl cells hne hcs hsize

/-- Lines of `.` and `O` of one common width deserialize to the `O` positions, row by row, with no warnings. -/
theorem deserializePlaintext_pattern_rows (lines : Array String) (w : Nat) (hl : IsRowLines lines w)
    (hls : lines.size * w < 2 ^ 31) (hne : 1 ≤ lines.size) :
    deserializePlaintext lines = ⟨#[], (linesCells lines 0).toArray.map cellBits⟩ :=
  deserializePlaintext_pattern_rows_Impl lines w hl hls hne

theorem deserializePlaintext_empty : deserializePlaintext #[] = ⟨#[], #[]⟩ :=
  deserializePlaintext_empty_Impl

theorem deserializePlaintext_comments_ignored :
    deserializePlaintext #["! comment", "O"] = ⟨#[], (#[(0, 0)] : Array (Int32 × Int32)).map cellBits⟩ :=
  deserializePlaintext_comments_ignored_Impl

/-- Serializing no cells gives a single dead cell, which reads back as no cells. -/
theorem plaintext_round_trip_empty :
    deserializePlaintext (serializePlaintext #[] 0 0 0 0) = ⟨#[], #[]⟩ :=
  plaintext_round_trip_empty_Impl

theorem plaintext_round_trip_glider :
    deserializePlaintext
        (serializePlaintext ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits)
          0 2 0 2) =
      ⟨#[], (#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ :=
  plaintext_round_trip_glider_Impl

/-- Blank lines, short lines and unexpected characters give warnings; unexpected characters other than spaces
are alive. -/
theorem deserializePlaintext_warnings :
    deserializePlaintext #["O.O", "", "O", "x O"] =
      ⟨#[.blankLine 2, .shortLine 3, .unexpectedChar 4 1 120, .unexpectedChar 4 2 32],
        (#[(0, 0), (2, 0), (0, 1), (0, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ :=
  deserializePlaintext_warnings_Impl

/-- A non-ASCII character counts as one character: one warning with its code point, and one alive cell. -/
theorem deserializePlaintext_non_ascii :
    deserializePlaintext #["OéO"] =
      ⟨#[.unexpectedChar 1 2 233], (#[(0, 0), (1, 0), (2, 0)] : Array (Int32 × Int32)).map cellBits⟩ :=
  deserializePlaintext_non_ascii_Impl

/-- Serialized cells are one row per line of the box, each of the box's width, of `.` and `O` only. -/
theorem serializePlaintext_rows (cells : Array UInt64) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hw : 1 ≤ (maxX - minX + 1).toUInt32.toNat) (hh : 1 ≤ (maxY - minY + 1).toUInt32.toNat)
    (hwh : (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    IsRowLines (serializePlaintext cells minX maxX minY maxY) (maxX - minX + 1).toUInt32.toNat ∧
      (serializePlaintext cells minX maxX minY maxY).size = (maxY - minY + 1).toUInt32.toNat :=
  serializePlaintext_rows_Impl cells minX maxX minY maxY hne hcs hw hh hwh

/--
Deserialization of any input is `linesSpec`: comment lines (starting with `!`) are skipped; a blank line gives a
warning unless it is the last line; each other line is a pattern row, where `.` is dead, `O` is alive and any other
character gives a warning and is alive unless it is a space; a row shorter than the longest gives a warning.
-/
theorem deserializePlaintext_eq_linesSpec (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 31) :
    deserializePlaintext lines =
      ⟨(linesSpec lines.toList 0 0 none).1.toArray, (linesSpec lines.toList 0 0 none).2.toArray.map cellBits⟩ :=
  deserializePlaintext_eq_linesSpec_Impl lines hls hb

end Algorithm

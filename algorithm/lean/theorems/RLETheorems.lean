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
import proofs.RLESpecProofs

namespace Algorithm

/-!
# RLE Master Theorems

The rule is checked by its digit sets in both notations, for every pair of digit lists; and concrete checks of
the format, including round trips. Every cell array inside its bounding box reads back exactly.
-/

open Classical in
/-- A rule `B<birth>/S<survival>` is Conway's rules exactly when the birth digits are {3} and the survival digits
are {2, 3}, in any order and with repeats, with letters of either case. -/
theorem checkRLERule_letters (pre b s : List UInt8) (cB cS : UInt8) (hcB : cB = 66 ∨ cB = 98)
    (hcS : cS = 83 ∨ cS = 115) (hb : b ≠ []) (hs : s ≠ []) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hsz : pre.length + b.length + s.length + 3 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) ∧ ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) then 0 else 3 :=
  checkRLERule_letters_Impl pre b s cB cS hcB hcS hb hs hbd hsd hsz

open Classical in
/-- A rule `<survival>/<birth>` is Conway's rules exactly when the survival digits are {2, 3} and the birth digits
are {3}, in any order and with repeats. -/
theorem checkRLERule_digits (pre s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : pre.length + s.length + b.length + 1 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ (s ++ 47 :: b)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ (s ++ 47 :: b)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 3 :=
  checkRLERule_digits_Impl pre s b hs hb hsd hbd hsz

theorem deserializeRLE_empty :
    deserializeRLE #[] = ⟨.emptyFile, #[.emptyFile], #[]⟩ :=
  deserializeRLE_empty_Impl

/-- The rule digits are sets: their order and repeats don't matter, in both rule notations. -/
theorem parseRLEHeader_rule_digit_sets :
    parseRLEHeader "x = 1, y = 1, rule = B3/S23".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1, rule = B3/S32".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1, rule = b33/s322".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1, rule = 23/3".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1, rule = 32/3".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1".toByteArray = 0 ∧
      parseRLEHeader "x = 1, y = 1, rule = B3/S234".toByteArray = 3 ∧
      parseRLEHeader "x = 1, y = 1, rule = 23/34".toByteArray = 3 ∧
      parseRLEHeader "x = 1, y = 1, rule = B3/S".toByteArray = 2 ∧
      parseRLEHeader "x = -1, y = 1".toByteArray = 2 :=
  parseRLEHeader_rule_digit_sets_Impl

/-- A run count that doesn't fit in an `Int32` is rejected rather than wrapped. -/
theorem deserializeRLE_out_of_range_count :
    deserializeRLE #["x = 1, y = 1", "4294967297o!"] = ⟨.unexpectedInput "4294967297" 2 1, #[], #[]⟩ :=
  deserializeRLE_out_of_range_count_Impl

/-- A count before `!` is reported as written, at its first digit. -/
theorem deserializeRLE_count_before_end :
    (deserializeRLE #["x = 1, y = 1", "o007!"]).warnings = #[.unexpectedInput 2 2 "007!"] :=
  deserializeRLE_count_before_end_Impl

/-- A count at the end of a line is dropped, so a `!` on the next line has no count. -/
theorem deserializeRLE_count_at_line_end :
    deserializeRLE #["x = 1, y = 1", "o12", "!"] =
      ⟨.ok, #[], ((#[(0, 0)] : Array (Int32 × Int32)).map cellBits)⟩ :=
  deserializeRLE_count_at_line_end_Impl

/-- A non-ASCII character is one character: one warning with its code point, at its character index. -/
theorem deserializeRLE_non_ascii :
    deserializeRLE #["x = 3, y = 1", "oéo!"] =
      ⟨.ok, #[.unexpectedChar 2 2 233],
        ((#[(0, 0), (1, 0), (2, 0)] : Array (Int32 × Int32)).map cellBits)⟩ :=
  deserializeRLE_non_ascii_Impl

theorem serializeRLE_empty : serializeRLE #[] 0 0 0 0 = #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"] :=
  serializeRLE_empty_Impl

theorem serializeRLE_glider :
    serializeRLE ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits) 0 2 0 2 =
      #["#R 0 0", "x = 3, y = 3, rule = B3/S23", "bo$2bo$3o!"] :=
  serializeRLE_glider_Impl

/-- Empty rows are merged into one end of row with a count. -/
theorem serializeRLE_empty_rows :
    serializeRLE ((#[(0, 0), (0, 3)] : Array (Int32 × Int32)).map cellBits) 0 0 0 3 =
      #["#R 0 0", "x = 1, y = 4, rule = B3/S23", "o3$o!"] :=
  serializeRLE_empty_rows_Impl

/--
Deserializing serialized cells succeeds with no warnings and gives back exactly the cells, at their own
coordinates, for every cell array inside its bounding box (of fewer than 2 ^ 25 cells).
-/
theorem rle_round_trip_box (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : 64 * ((maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1)) < 2 ^ 31) :
    (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).status = .ok ∧
      (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).cells ↔ q ∈ cells :=
  rle_round_trip_box_Impl cells minX maxX minY maxY hne hcs hbox hsize

/--
Round trip of whole patterns: the serializer computes the bounding box itself, and deserializing gives back exactly
the cells, with no warnings, for every non-empty cell array whose bounding box has fewer than 2 ^ 25 cells.
-/
theorem rle_round_trip_cells (cells : Array (Int32 × Int32)) (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hsize : ∀ c ∈ cells, ∀ d ∈ cells, ∀ e ∈ cells, ∀ f ∈ cells,
      64 * ((c.1.toInt - d.1.toInt + 1) * (e.2.toInt - f.2.toInt + 1)) < 2 ^ 31) :
    (deserializeRLE (serializeRLECells (cells.map cellBits))).status = .ok ∧
      (deserializeRLE (serializeRLECells (cells.map cellBits))).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializeRLE (serializeRLECells (cells.map cellBits))).cells ↔ q ∈ cells :=
  rle_round_trip_cells_Impl cells hne hcs hsize

theorem rle_round_trip_glider :
    deserializeRLE
        (serializeRLE ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits) 0 2 0 2) =
      ⟨.ok, #[], ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits)⟩ :=
  rle_round_trip_glider_Impl

theorem rle_round_trip_offset :
    deserializeRLE (serializeRLE ((#[(-1, 5), (0, 5), (1, 5)] : Array (Int32 × Int32)).map cellBits) (-1) 1 5 5) =
      ⟨.ok, #[], ((#[(-1, 5), (0, 5), (1, 5)] : Array (Int32 × Int32)).map cellBits)⟩ :=
  rle_round_trip_offset_Impl

/-- Every line of a serialized pattern has at most 70 bytes, as the format requires. -/
theorem rle_lines_le_70 (cells : Array (Int32 × Int32)) (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hsize : ∀ c ∈ cells, ∀ d ∈ cells, ∀ e ∈ cells, ∀ f ∈ cells,
      64 * ((c.1.toInt - d.1.toInt + 1) * (e.2.toInt - f.2.toInt + 1)) < 2 ^ 31) :
    ∀ l ∈ serializeRLECells (cells.map cellBits), l.toByteArray.size ≤ 70 :=
  rle_lines_le_70_Impl cells hne hcs hsize

/--
Deserialization of any input is `rleSpec`: comment lines (`#`, where `#R x y` sets the offset), the
`x = w, y = h[, rule = r]` header, and then the pattern characters (`rleLineSpec`): counts, `b`, `o` and `$` runs,
whitespace, and `!`; the cells are the decoded runs. This holds for inputs of fewer than 2 ^ 30 bytes whose pattern
has fewer than 2 ^ 31 alive cells.
-/
theorem deserializeRLE_eq_rleSpec (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 30) (hc : (rleSpec lines.toList).cells.size < 2 ^ 31) :
    deserializeRLE lines = rleSpec lines.toList :=
  deserializeRLE_eq_rleSpec_Impl lines hls hb hc

end Algorithm

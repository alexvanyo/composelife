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
# RLE Master Theorems

The rule is checked by its digit sets in both notations, for every pair of digit lists; and concrete checks of
the format, including round trips. Every cell array inside its bounding box reads back exactly.
-/

open Classical in
/-- A rule `B<birth>/S<survival>` is Conway's rules exactly when the birth digits are {3} and the survival digits
are {2, 3}, in any order and with repeats, with letters of either case. -/
theorem checkRLERule_letters_spec (pre b s : List UInt8) (cB cS : UInt8) (hcB : cB = 66 ∨ cB = 98)
    (hcS : cS = 83 ∨ cS = 115) (hb : b ≠ []) (hs : s ≠ []) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hsz : pre.length + b.length + s.length + 3 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ cB :: (b ++ 47 :: cS :: s)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) ∧ ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) then 0 else 3 :=
  checkRLERule_letters pre b s cB cS hcB hcS hb hs hbd hsd hsz

open Classical in
/-- A rule `<survival>/<birth>` is Conway's rules exactly when the survival digits are {2, 3} and the birth digits
are {3}, in any order and with repeats. -/
theorem checkRLERule_digits_spec (pre s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : pre.length + s.length + b.length + 1 < 2 ^ 32) :
    checkRLERule ⟨(pre ++ (s ++ 47 :: b)).toArray⟩ pre.length.toUInt32
        (⟨(pre ++ (s ++ 47 :: b)).toArray⟩ : ByteArray).size.toUInt32 =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 3 :=
  checkRLERule_digits pre s b hs hb hsd hbd hsz

theorem deserializeRLE_empty :
    deserializeRLE #[] = ⟨1, "", 0, 0, #[⟨0, 0, 0, 0, "", 0, 0⟩], #[]⟩ := by
  decide +kernel

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
      parseRLEHeader "x = -1, y = 1".toByteArray = 2 := by
  decide +kernel

/-- A run count that doesn't fit in an `Int32` is rejected rather than wrapped. -/
theorem deserializeRLE_out_of_range_count :
    deserializeRLE #["x = 1, y = 1", "4294967297o!"] = ⟨4, "4294967297", 2, 1, #[], #[]⟩ := by
  decide +kernel

/-- A count before `!` is reported as written, at its first digit. -/
theorem deserializeRLE_count_before_end :
    (deserializeRLE #["x = 1, y = 1", "o007!"]).warnings = #[⟨3, 2, 2, 0, "007!", 0, 0⟩] := by
  decide +kernel

/-- A count at the end of a line is dropped, so a `!` on the next line has no count. -/
theorem deserializeRLE_count_at_line_end :
    deserializeRLE #["x = 1, y = 1", "o12", "!"] = ⟨0, "", 0, 0, #[], #[(0, 0)]⟩ := by
  decide +kernel

/-- A non-ASCII character is one character: one warning with its code point, at its character index. -/
theorem deserializeRLE_non_ascii :
    deserializeRLE #["x = 3, y = 1", "oéo!"] =
      ⟨0, "", 0, 0, #[⟨2, 2, 2, 233, "", 0, 0⟩], #[(0, 0), (1, 0), (2, 0)]⟩ := by
  decide +kernel

theorem serializeRLE_empty : serializeRLE #[] 0 0 0 0 = #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"] := by
  decide +kernel

theorem serializeRLE_glider :
    serializeRLE #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2 =
      #["#R 0 0", "x = 3, y = 3, rule = B3/S23", "bo$2bo$3o!"] := by
  decide +kernel

/-- Empty rows are merged into one end of row with a count. -/
theorem serializeRLE_empty_rows :
    serializeRLE #[(0, 0), (0, 3)] 0 0 0 3 = #["#R 0 0", "x = 1, y = 4, rule = B3/S23", "o3$o!"] := by
  decide +kernel

/--
Deserializing serialized cells succeeds with no warnings and gives back exactly the cells, at their own
coordinates, for every cell array inside its bounding box (of fewer than 2 ^ 25 cells).
-/
theorem rle_round_trip_spec (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : 64 * ((maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1)) < 2 ^ 31) :
    (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).status = 0 ∧
      (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, q ∈ (deserializeRLE (serializeRLE (cells.map cellBits) minX maxX minY maxY)).cells ↔ q ∈ cells :=
  rle_round_trip_box cells minX maxX minY maxY hne hcs hbox hsize

theorem rle_round_trip_glider :
    deserializeRLE (serializeRLE #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] 0 2 0 2) =
      ⟨0, "", 0, 0, #[], #[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)]⟩ := by
  decide +kernel

theorem rle_round_trip_offset :
    deserializeRLE (serializeRLE #[(-1, 5), (0, 5), (1, 5)] (-1) 1 5 5) =
      ⟨0, "", 0, 0, #[], #[(-1, 5), (0, 5), (1, 5)]⟩ := by
  decide +kernel

end Algorithm

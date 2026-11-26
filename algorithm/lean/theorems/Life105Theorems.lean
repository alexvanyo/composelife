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
import proofs.Life105SplitProofs
import proofs.Life105SpecProofs

namespace Algorithm

/-!
# Life 1.05 Master Theorems

The rule line is checked by its digit sets, for every pair of digit lists. Serializing whole patterns round-trips
exactly. And concrete checks of the format.
-/

open Classical in
/-- A `#R survival/birth` line is Conway's rules exactly when the survival digits are {2, 3} and the birth digits
are {3}, in any order and with repeats. -/
theorem checkRuleLine_digits (s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : s.length + b.length + 4 < 2 ^ 32) :
    checkRuleLine ⟨(35 :: 82 :: 32 :: (s ++ 47 :: b)).toArray⟩ =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 2 :=
  checkRuleLine_digits_Impl s b hs hb hsd hbd hsz

/-- A file of serialized blocks deserializes, with no warnings, to the alive cells of the blocks, in order. -/
theorem deserializeLife105_serialized_blocks (bs : List Life105Block)
    (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray) =
      ⟨.ok, #[], (bs.flatMap Life105Block.cells).toArray.map cellBits⟩ :=
  deserializeLife105_serialized_blocks_Impl bs hbs hsz

/-- Round trip: the cells read back are exactly the cells of the blocks that are inside their block. -/
theorem life105_round_trip (bs : List Life105Block)
    (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    let r := deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray)
    r.status = .ok ∧ r.warnings = #[] ∧
      ∀ q, cellBits q ∈ r.cells ↔ ∃ b ∈ bs, ∃ c ∈ b.1,
        (gridIndex b.2.1 b.2.2.1 80 (b.2.2.2 - b.2.2.1 + 1).toUInt32
          ((cellKeyX c).toInt32, (cellKeyY c).toInt32)).isSome ∧
          q = ((cellKeyX c).toInt32, (cellKeyY c).toInt32) :=
  life105_round_trip_Impl bs hbs hsz

/--
Round trip of whole patterns: `serializeLife105` covers the cells with blocks of 80 columns, and deserializing its
lines succeeds with no warnings and gives back exactly the cells. `h` bounds the differences of the y coordinates.
-/
theorem life105_full_round_trip (cells : Array (Int32 × Int32)) (h : Nat) (hc : cells.size < 2 ^ 31)
    (hy : ∀ c ∈ cells, ∀ d ∈ cells, c.2.toInt - d.2.toInt < h)
    (hsz : 80 * (cells.size * (h + 1) + 2) < 2 ^ 31) :
    let r := deserializeLife105 (serializeLife105 (cells.map cellBits))
    r.status = .ok ∧ r.warnings = #[] ∧ ∀ q, cellBits q ∈ r.cells ↔ q ∈ cells :=
  life105_full_round_trip_Impl cells h hc hy hsz

/-- Every block header line parses back to its coordinates. -/
theorem parseBlockHeader_round_trip (x y : Int32) :
    parseBlockHeader (formatBlockHeader x y).toByteArray = some ⟨x, y⟩ :=
  parseBlockHeader_round_trip_Impl x y

theorem deserializeLife105_empty :
    deserializeLife105 #[] = ⟨.ok, #[.emptyFile], #[]⟩ :=
  deserializeLife105_empty_Impl

theorem deserializeLife105_invalid_header :
    deserializeLife105 #["#Life 1.06"] = ⟨.invalidHeader "#Life 1.06", #[], #[]⟩ :=
  deserializeLife105_invalid_header_Impl

/-- The rule digits are sets: their order and repeats don't matter. -/
theorem checkRuleLine_digit_sets :
    checkRuleLine "#R 23/3".toByteArray = 0 ∧ checkRuleLine "#R 32/3".toByteArray = 0 ∧
      checkRuleLine "#R 3223/33".toByteArray = 0 ∧ checkRuleLine "#R 23/36".toByteArray = 2 ∧
      checkRuleLine "#R 2/3".toByteArray = 2 ∧ checkRuleLine "#R 23".toByteArray = 1 ∧
      checkRuleLine "#R /3".toByteArray = 1 :=
  checkRuleLine_digit_sets_Impl

/-- A block offset that doesn't fit in an `Int32` is rejected rather than wrapped. -/
theorem deserializeLife105_out_of_range_offset :
    (deserializeLife105 #["#Life 1.05", "#P 4294967297 0", "*"]).status =
      .unexpectedInput "#P 4294967297 0" 2 3 :=
  deserializeLife105_out_of_range_offset_Impl

theorem life105_block_round_trip_glider :
    deserializeLife105
        (#["#Life 1.05", "#N"] ++
          serializeLife105Block ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits)
            0 0 2) =
      ⟨.ok, #[], (#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ :=
  life105_block_round_trip_glider_Impl

/-- Cells outside the block are left for another block. -/
theorem serializeLife105Block_skips_outside :
    serializeLife105Block ((#[(0, 0), (80, 0)] : Array (Int32 × Int32)).map cellBits) 0 0 0 =
      #["#P 0 0", "*" ++ String.ofList (List.replicate 79 '.')] :=
  serializeLife105Block_skips_outside_Impl

/-- Every serialized line is a header line, a `#P` block line or a row of 80 `.` and `*` characters. -/
theorem serializeLife105_lines (cells : Array (Int32 × Int32)) (h : Nat) (hc : cells.size < 2 ^ 31)
    (hy : ∀ c ∈ cells, ∀ d ∈ cells, c.2.toInt - d.2.toInt < h)
    (hsz : 80 * (cells.size * (h + 1) + 2) < 2 ^ 31) :
    ∀ l ∈ serializeLife105 (cells.map cellBits), l = "#Life 1.05" ∨ l = "#N" ∨
      (∃ x y, l = formatBlockHeader x y) ∨ (l.toByteArray.size = 80 ∧ IsRow105 l.toByteArray) :=
  serializeLife105_lines_Impl cells h hc hy hsz

/--
Deserialization of any input is `life105Spec`: the `#Life 1.05` header, `#D` description lines, an optional `#N`
or `#R` rule line, and then blocks, each a `#P x y` line followed by rows of `.` and `*`; the first other line is
an error.
-/
theorem deserializeLife105_eq_life105Spec (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 31) :
    deserializeLife105 lines = life105Spec lines.toList :=
  deserializeLife105_eq_life105Spec_Impl lines hls hb

end Algorithm

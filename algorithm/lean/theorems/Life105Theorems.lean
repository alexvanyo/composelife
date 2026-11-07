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

The rule line is checked by its digit sets, for every pair of digit lists; and concrete checks of the format.
-/

open Classical in
/-- A `#R survival/birth` line is Conway's rules exactly when the survival digits are {2, 3} and the birth digits
are {3}, in any order and with repeats. -/
theorem checkRuleLine_spec (s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : s.length + b.length + 4 < 2 ^ 32) :
    checkRuleLine ⟨(35 :: 82 :: 32 :: (s ++ 47 :: b)).toArray⟩ =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 2 :=
  checkRuleLine_digits s b hs hb hsd hbd hsz

/-- A file of serialized blocks deserializes, with no warnings, to the alive cells of the blocks, in order. -/
theorem deserializeLife105_serialized_blocks (bs : List Life105Block)
    (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray) =
      ⟨0, "", 0, 0, #[], (bs.flatMap Life105Block.cells).toArray.map cellBits⟩ :=
  deserializeLife105_blocks bs hbs hsz

/-- Round trip: the cells read back are exactly the cells of the blocks that are inside their block. -/
theorem life105_round_trip_spec (bs : List Life105Block)
    (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    let r := deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray)
    r.status = 0 ∧ r.warnings = #[] ∧
      ∀ q, cellBits q ∈ r.cells ↔ ∃ b ∈ bs, ∃ c ∈ b.1,
        (gridIndex b.2.1 b.2.2.1 80 (b.2.2.2 - b.2.2.1 + 1).toUInt32 ((cellKeyX c).toInt32, (cellKeyY c).toInt32)).isSome ∧
          q = ((cellKeyX c).toInt32, (cellKeyY c).toInt32) :=
  life105_round_trip bs hbs hsz

/-- Every block header line parses back to its coordinates. -/
theorem parseBlockHeader_round_trip (x y : Int32) :
    parseBlockHeader (formatBlockHeader x y).toByteArray = some ⟨x, y⟩ :=
  parseBlockHeader_format x y

theorem deserializeLife105_empty :
    deserializeLife105 #[] = ⟨0, "", 0, 0, #[⟨0, "", 0, 0⟩], #[]⟩ := by
  decide +kernel

theorem deserializeLife105_invalid_header :
    deserializeLife105 #["#Life 1.06"] = ⟨1, "#Life 1.06", 1, 0, #[], #[]⟩ := by
  decide +kernel

/-- The rule digits are sets: their order and repeats don't matter. -/
theorem checkRuleLine_digit_sets :
    checkRuleLine "#R 23/3".toByteArray = 0 ∧ checkRuleLine "#R 32/3".toByteArray = 0 ∧
      checkRuleLine "#R 3223/33".toByteArray = 0 ∧ checkRuleLine "#R 23/36".toByteArray = 2 ∧
      checkRuleLine "#R 2/3".toByteArray = 2 ∧ checkRuleLine "#R 23".toByteArray = 1 ∧
      checkRuleLine "#R /3".toByteArray = 1 := by
  decide +kernel

/-- A block offset that doesn't fit in an `Int32` is rejected rather than wrapped. -/
theorem deserializeLife105_out_of_range_offset :
    (deserializeLife105 #["#Life 1.05", "#P 4294967297 0", "*"]).status = 3 := by
  decide +kernel

theorem life105_block_round_trip_glider :
    deserializeLife105
        (#["#Life 1.05", "#N"] ++
          serializeLife105Block ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits)
            0 0 2) =
      ⟨0, "", 0, 0, #[], (#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ := by
  decide +kernel

/-- Cells outside the block are left for another block. -/
theorem serializeLife105Block_skips_outside :
    serializeLife105Block ((#[(0, 0), (80, 0)] : Array (Int32 × Int32)).map cellBits) 0 0 0 =
      #["#P 0 0", "*" ++ String.ofList (List.replicate 79 '.')] := by
  decide +kernel

end Algorithm

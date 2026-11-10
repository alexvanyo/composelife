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

Full specifications of Life 1.06 serialization and deserialization, the round trip for every coordinate array,
and rejection of coordinates that don't fit in an `Int32`.
-/

/-- Integer parsing reads an optional minus sign and then as many digits as there are, and fails if there are
no digits or the value doesn't fit in an `Int32`. -/
theorem parseInt32At_eq (b : ByteArray) (hb : b.size < 2 ^ 32) (pos : UInt32) (hp : pos.toNat ≤ b.size) :
    parseInt32At b pos b.size.toUInt32 =
      (parseInt32Spec (bytesFrom b pos.toNat)).map (fun r => ⟨r.1, pos + r.2.toUInt32⟩) :=
  parseInt32At_spec b hb pos hp

/-- Integer parsing reads back the decimal form of every `Int32`. -/
theorem parseInt32Spec_of_toString (x : Int32) (rest : List UInt8)
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    parseInt32Spec ((toString x).toByteArray.data.toList ++ rest) =
      some (x, (toString x).toByteArray.data.toList.length) :=
  parseInt32Spec_toString x rest hrest

/-- Serialization is the header followed by one `x y` line per cell (given by its key), in order. -/
theorem serializeLife106_spec (cells : Array UInt64) (hc : cells.size + 2 < 2 ^ 31) :
    serializeLife106 cells = #["#Life 1.06"] ++ cells.map (fun k => formatCoordLine (cellKeyX k) (cellKeyY k)) :=
  serializeLife106_eq cells hc

/-- Deserialization reports an empty file, a bad header or the first line that isn't a coordinate pair, and
otherwise returns the keys of the coordinates of every line, in order. -/
theorem deserializeLife106_spec (lines : Array String) (hl : lines.size < 2 ^ 31) :
    deserializeLife106 lines =
      if lines.size = 0 then ⟨.emptyFile, #[]⟩
      else if lines[0]! ≠ "#Life 1.06" then ⟨.invalidHeader lines[0]!, #[]⟩
      else
        match (lines.toList.drop 1).mapM parseCoordLine with
        | some cells => ⟨.ok, (cells.map cellBits).toArray⟩
        | none =>
          let j := (lines.toList.drop 1).findIdx (fun l => (parseCoordLine l).isNone)
          ⟨.invalidLine ((j + 2).toUInt32) lines[j + 1]!, #[]⟩ :=
  deserializeLife106_eq lines hl

/-- Every coordinate line parses back to its cell. -/
theorem parseCoordLine_format (c : Int32 × Int32) :
    parseCoordLine (formatCoordLine c.1.toUInt32 c.2.toUInt32) = some c :=
  parseCoordLine_formatCoordLine c

/-- Deserializing serialized cells gives back exactly those cells, in order. -/
theorem deserializeLife106_round_trip (cells : Array (Int32 × Int32)) (hc : cells.size + 2 < 2 ^ 31) :
    deserializeLife106 (serializeLife106 (cells.map cellBits)) = ⟨.ok, cells.map cellBits⟩ :=
  deserializeLife106_serializeLife106 cells hc

/-- A coordinate line whose first number doesn't fit in an `Int32` is rejected rather than wrapped. -/
theorem parseCoordLine_rejects_out_of_range (neg : Bool) (n : Nat) (rest : String)
    (hn : if neg then 2 ^ 31 < n else 2 ^ 31 ≤ n)
    (hsz : ((if neg then "-" else "") ++ toString n ++ rest).toByteArray.size < 2 ^ 32)
    (hrest : ∀ y, rest.toByteArray.data.toList.head? = some y → isDigitByte y = false) :
    parseCoordLine ((if neg then "-" else "") ++ toString n ++ rest) = none :=
  parseCoordLine_first_out_of_range neg n rest hn hsz hrest

/-- An empty line sequence produces the empty file status. -/
theorem deserializeLife106_empty : deserializeLife106 #[] = ⟨.emptyFile, #[]⟩ := by
  decide +kernel

/-- Deserializing a valid header with a single coordinate recovers the coordinate. -/
theorem deserializeLife106_single_coord :
    deserializeLife106 #["#Life 1.06", "10 -20"] = ⟨.ok, #[cellBits (10, -20)]⟩ := by
  decide +kernel

/-- The extreme `Int32` values parse. -/
theorem deserializeLife106_extremes :
    deserializeLife106 #["#Life 1.06", "-2147483648 2147483647"] =
      ⟨.ok, #[cellBits (-2147483648, 2147483647)]⟩ := by
  decide +kernel

/-- A value that would wrap around to a valid coordinate is rejected. -/
theorem deserializeLife106_wrapping_value :
    deserializeLife106 #["#Life 1.06", "4294967297 0"] = ⟨.invalidLine 2 "4294967297 0", #[]⟩ := by
  decide +kernel

end Algorithm

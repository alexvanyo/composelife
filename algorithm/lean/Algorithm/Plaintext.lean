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

import Algorithm.SerialCore

namespace Algorithm

/-!
# Plaintext

Rows of `.` (dead) and `O` (alive) characters. Lines starting with `!` are comments.

Lines are read as UTF-8, and columns count characters.
-/

@[kotlin_class "PlaintextWarning"]
structure PlaintextWarning where
  /-- 0: unexpected blank line, 1: unexpected short line, 2: unexpected character. -/
  tag : UInt32
  /-- 1-based line index. -/
  lineIndex : UInt32
  /-- 1-based character index, for unexpected characters. -/
  columnIndex : UInt32
  /-- The code point, for unexpected characters. -/
  charVal : UInt32
  deriving DecidableEq, Repr

@[kotlin_class "PlaintextResult"]
structure PlaintextResult where
  warnings : Array PlaintextWarning
  cells : Array (Int32 × Int32)
  deriving DecidableEq, Repr

/-- The number of characters in `bytes` from `p` on, plus `n`. -/
def countChars (bytes : ByteArray) (limit : UInt32) (p : UInt32) (n : UInt32) : UInt32 :=
  if h : p < limit then
    countChars bytes limit (decodeCharAt bytes p limit).2 (n + 1)
  else n
termination_by limit.toNat - p.toNat
decreasing_by have := decodeCharAt_next bytes p limit h; omega

/--
Reads lines `i` onward. In a pattern row (`inRow`), `bytes` is the current line, `p` the byte position and `col`
the character position. `longestIdx` and `longestLen` describe the longest pattern row so far, if any.
-/
def deserializePlaintext.loop (lines : Array String) (numLines : UInt32) (i : UInt32) (inRow : Bool)
    (bytes : ByteArray) (limit : UInt32) (p col : UInt32) (rowIdx : UInt32) (longestIdx longestLen : UInt32)
    (hasLongest : Bool) (warns : GrowBuf PlaintextWarning) (cells : GrowBuf (Int32 × Int32)) :
    PlaintextResult :=
  if hi : i < numLines then
    have hi1 : numLines.toNat - (i + 1).toNat < numLines.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp hi
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt numLines
        simp only [UInt32.toNat_one]
        omega
      omega
    if inRow then
      if hp : p < limit then
        let r := decodeCharAt bytes p limit
        have := decodeCharAt_next bytes p limit hp
        let cp := r.1
        if cp == 46 then -- '.'
          deserializePlaintext.loop lines numLines i true bytes limit r.2 (col + 1) rowIdx longestIdx longestLen
            hasLongest warns cells
        else if cp == 79 then -- 'O'
          deserializePlaintext.loop lines numLines i true bytes limit r.2 (col + 1) rowIdx longestIdx longestLen
            hasLongest warns (cells.push (col.toInt32, rowIdx.toInt32))
        else
          -- Anything else is a warning, and alive unless it is a space.
          let newWarns := warns.push ⟨2, i + 1, col + 1, cp⟩
          let newCells := if cp == 32 then cells else cells.push (col.toInt32, rowIdx.toInt32)
          deserializePlaintext.loop lines numLines i true bytes limit r.2 (col + 1) rowIdx longestIdx longestLen
            hasLongest newWarns newCells
      else
        deserializePlaintext.loop lines numLines (i + 1) false bytes limit 0 0 (rowIdx + 1) longestIdx longestLen
          hasLongest warns cells
    else
      let bytes := lines[i.toNat]!.toByteArray
      let limit := bytes.size.toUInt32
      if limit == 0 then
        let newWarns := if i + 1 < numLines then warns.push ⟨0, i + 1, 0, 0⟩ else warns
        deserializePlaintext.loop lines numLines (i + 1) false bytes limit 0 0 rowIdx longestIdx longestLen
          hasLongest newWarns cells
      else if bytes.get! 0 == 33 then -- '!'
        deserializePlaintext.loop lines numLines (i + 1) false bytes limit 0 0 rowIdx longestIdx longestLen
          hasLongest warns cells
      else
        let len := countChars bytes limit 0 0
        if !hasLongest then
          deserializePlaintext.loop lines numLines i true bytes limit 0 0 rowIdx (i + 1) len true warns cells
        else if len > longestLen then
          deserializePlaintext.loop lines numLines i true bytes limit 0 0 rowIdx (i + 1) len true
            (warns.push ⟨1, longestIdx, 0, 0⟩) cells
        else
          let lenWarns := if len < longestLen then warns.push ⟨1, i + 1, 0, 0⟩ else warns
          deserializePlaintext.loop lines numLines i true bytes limit 0 0 rowIdx longestIdx longestLen true
            lenWarns cells
  else ⟨warns.toArray, cells.toArray⟩
termination_by (numLines.toNat - i.toNat) * 2 ^ 33 + (if inRow then limit.toNat - p.toNat else 2 ^ 32)
decreasing_by
  all_goals
    simp_all only [ite_true, Bool.false_eq_true, ite_false]
    first
      | omega
      | (have := UInt32.toNat_lt limit; omega)
      | (have := UInt32.toNat_lt (ByteArray.size lines[i.toNat]!.toByteArray).toUInt32; omega)

@[export plaintext_deserialize]
def deserializePlaintext (lines : Array String) : PlaintextResult :=
  deserializePlaintext.loop lines lines.size.toUInt32 0 false ByteArray.empty 0 0 0 0 0 0 false GrowBuf.empty
    GrowBuf.empty

/--
Serializes the cells (as `cellBits`) in the bounding box from (`minX`, `minY`) to (`maxX`, `maxY`), one row per
line. Cells
outside the box are skipped.
-/
@[export plaintext_serialize]
def serializePlaintext (cells : Array (UInt32 × UInt32)) (minX maxX minY maxY : Int32) : Array String :=
  if cells.size.toUInt32 == 0 then #["."]
  else
    let width : UInt32 := (maxX - minX + 1).toUInt32
    let height : UInt32 := (maxY - minY + 1).toUInt32
    let grid := fillGrid cells minX minY width height 79 (by decide) 0 cells.size.toUInt32
      (AsciiBytes.replicate (width * height) 46 (by decide))
    (gridRows grid width height 0 GrowBuf.empty).toArray

end Algorithm

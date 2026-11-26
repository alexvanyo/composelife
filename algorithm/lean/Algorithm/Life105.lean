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

set_option compiler.kotlin.typedArrays true

namespace Algorithm

/-!
# Life 1.05

A `#Life 1.05` header, `#D` description lines, an optional `#N` or `#R survival/birth` rule line, and blocks: a
`#P x y` line followed by rows of `.` (dead) and `*` (alive).
-/

/-- A problem that deserialization recovered from. -/
@[kotlin_class "sealed class Life105Warning"]
inductive Life105Warning where
  | emptyFile
  /-- Unexpected input in `line`, line `lineIndex` (1-based), at column `columnIndex`. -/
  | unexpectedInput (line : String) (lineIndex columnIndex : UInt32)
  deriving DecidableEq, Repr

/-- How deserialization ended. -/
@[kotlin_class "sealed class Life105Status"]
inductive Life105Status where
  | ok
  /-- The first line is not the `#Life 1.05` header. -/
  | invalidHeader (line : String)
  /-- The rule line is not Conway's rules. -/
  | ruleNotSupported
  /-- Unexpected input in `line`, line `lineIndex` (1-based), at column `columnIndex`. -/
  | unexpectedInput (line : String) (lineIndex columnIndex : UInt32)
  deriving DecidableEq, Repr

@[kotlin_class "Life105Result"]
structure Life105Result where
  status : Life105Status
  warnings : Array Life105Warning
  /-- The keys (`cellBits`) of the cells. -/
  cells : Array UInt64
  deriving DecidableEq, Repr

/--
Checks a `#R survival/birth` rule line: 0 for Conway's rules (survival digits {2, 3} and birth digits {3}, in
any order and with repeats), 1 if it is malformed, and 2 for any other rule.
-/
def checkRuleLine (bytes : ByteArray) : UInt32 :=
  let limit := bytes.size.toUInt32
  if limit < 3 || bytes.get! 0 != 35 || bytes.get! 1 != 82 || bytes.get! 2 != 32 then 1 -- "#R "
  else
    let (e1, survival) := scanDigitSet bytes limit 3 0
    if e1 == 3 || !(e1 < limit) || bytes.get! e1.toNat != 47 then 1 -- '/'
    else
      let (e2, birth) := scanDigitSet bytes limit (e1 + 1) 0
      if e2 == e1 + 1 || e2 != limit then 1
      else if survival == survival23Mask && birth == birth3Mask then 0
      else 2

/-- Parses a `#P x y` block header. -/
def parseBlockHeader (bytes : ByteArray) : Option ParsedCoords :=
  let limit := bytes.size.toUInt32
  if limit < 3 || bytes.get! 0 != 35 || bytes.get! 1 != 80 || bytes.get! 2 != 32 then none -- "#P "
  else
    match parseInt32At bytes 3 limit with
    | none => none
    | some r1 =>
      if r1.next < limit && bytes.get! r1.next.toNat == 32 then
        match parseInt32At bytes (r1.next + 1) limit with
        | none => none
        | some r2 => if r2.next == limit then some ⟨r1.val, r2.val⟩ else none
      else none

/-- Whether bytes `p` onward are all `.` or `*`. -/
def isRowRest (bytes : ByteArray) (limit : UInt32) (p : UInt32) : Bool :=
  if h : p < limit then
    have : limit.toNat - (p + 1).toNat < limit.toNat - p.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (p + 1).toNat = p.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let b := bytes.get! p.toNat
    if b == 46 || b == 42 then isRowRest bytes limit (p + 1) else false
  else true
termination_by limit.toNat - p.toNat

/-- Whether a line is a nonempty row of `.` and `*`. -/
def isRowLine (bytes : ByteArray) : Bool :=
  bytes.size.toUInt32 != 0 && isRowRest bytes bytes.size.toUInt32 0

/-- Whether a line starts with `#` and then `c`. -/
@[inline]
def startsWithHash (bytes : ByteArray) (c : UInt8) : Bool :=
  bytes.size.toUInt32 >= 2 && bytes.get! 0 == 35 && bytes.get! 1 == c

/-- The index of the first line from `i` on that isn't a `#D` description line. -/
def skipDescriptions (lines : Array String) (numLines : UInt32) (i : UInt32) : UInt32 :=
  if h : i < numLines then
    have : numLines.toNat - (i + 1).toNat < numLines.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt numLines
        simp only [UInt32.toNat_one]
        omega
      omega
    if startsWithHash lines[i.toNat]!.toByteArray 68 then skipDescriptions lines numLines (i + 1) else i
  else i
termination_by numLines.toNat - i.toNat

/--
Reads the blocks in lines `i` onward. In a row (`inRow`), `bytes` is the current line and `p` the byte position;
the row is at `blockY + rowIndex`.
-/
def parseBlocks (lines : Array String) (numLines : UInt32) (i : UInt32) (inRow : Bool) (bytes : ByteArray)
    (limit p : UInt32) (hasBlock : Bool) (blockX blockY : Int32) (rowIndex : Int32) (warns : Array Life105Warning)
    (cells : U64Buf) : Life105Result :=
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
        have hp1 : limit.toNat - (p + 1).toNat < limit.toNat - p.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp hp
          have h2 : (p + 1).toNat = p.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let newCells :=
          if bytes.get! p.toNat == 42 then U64Buf.push cells (cellBits (blockX + p.toInt32, blockY + rowIndex))
          else cells
        parseBlocks lines numLines i true bytes limit (p + 1) hasBlock blockX blockY rowIndex warns newCells
      else
        parseBlocks lines numLines (i + 1) false bytes limit 0 hasBlock blockX blockY (rowIndex + 1) warns cells
    else
      let line := lines[i.toNat]!
      let bytes := line.toByteArray
      if startsWithHash bytes 80 then -- "#P"
        match parseBlockHeader bytes with
        | none => ⟨.unexpectedInput line (i + 1) 3, warns, noCells⟩
        | some c => parseBlocks lines numLines (i + 1) false bytes limit 0 true c.x c.y 0 warns cells
      else if isRowLine bytes && hasBlock then
        parseBlocks lines numLines i true bytes bytes.size.toUInt32 0 true blockX blockY rowIndex warns cells
      else
        ⟨.unexpectedInput line (i + 1) 1, warns, noCells⟩
  else
    ⟨.ok, warns, U64Buf.toArray cells⟩
termination_by (numLines.toNat - i.toNat) * 2 ^ 33 + (if inRow then limit.toNat - p.toNat else 2 ^ 32)
decreasing_by
  all_goals
    simp_all only [ite_true, Bool.false_eq_true, ite_false]
    first
      | omega
      | (have := UInt32.toNat_lt limit; omega)
      | (have := UInt32.toNat_lt (ByteArray.size lines[i.toNat]!.toByteArray).toUInt32; omega)

@[export life105_deserialize, kotlin_types "Array<String>" "_"]
def deserializeLife105 (lines : Array String) : Life105Result :=
  let numLines := lines.size.toUInt32
  if numLines == 0 then
    ⟨.ok, #[.emptyFile], noCells⟩
  else
    let header := lines[0]!
    if header != "#Life 1.05" then
      ⟨.invalidHeader header, #[], noCells⟩
    else
      let i := skipDescriptions lines numLines 1
      if i < numLines then
        let ruleLine := lines[i.toNat]!
        let bytes := ruleLine.toByteArray
        if startsWithHash bytes 78 then -- "#N"
          let warns := if ruleLine != "#N" then #[.unexpectedInput ruleLine (i + 1) 3] else #[]
          parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 warns U64Buf.empty
        else if startsWithHash bytes 82 then -- "#R"
          let status := checkRuleLine bytes
          if status == 0 then parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[] U64Buf.empty
          else if status == 1 then ⟨.unexpectedInput ruleLine (i + 1) 3, #[], noCells⟩
          else ⟨.ruleNotSupported, #[], noCells⟩
        else
          parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[] U64Buf.empty
      else
        ⟨.ok, #[], noCells⟩

/-- The block header line for a block at (`x`, `y`). -/
def formatBlockHeader (x y : Int32) : String := s!"#P {x} {y}"

/--
Serializes the block of cells from (`minX`, `minY`) to (`minX + 79`, `maxY`): the `#P` line and one row of 80
characters per line. Cells outside the block are skipped.
-/
@[export life105_serialize_block]
def serializeLife105Block (cells : Array UInt64) (minX minY maxY : Int32) : Array String :=
  let height : UInt32 := (maxY - minY + 1).toUInt32
  let grid := fillGrid cells minX minY 80 height 42 (by decide) 0 cells.size.toUInt32
    (AsciiBytes.replicate (80 * height) 46 (by decide))
  (gridRows grid 80 height 0 (GrowBuf.empty.push (formatBlockHeader minX minY))).toArray

/--
The least x, least y and greatest y of `minX`, `minY`, `maxY` and the cells `i` onward (as `cellBits`).
-/
def life105Bounds (cells : Array UInt64) (i limit : UInt32) (minX minY maxY : Int32) : Int32 × Int32 × Int32 :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let k := cells[i.toNat]!
    let x := (cellKeyX k).toInt32
    let y := (cellKeyY k).toInt32
    life105Bounds cells (i + 1) limit (if x < minX then x else minX) (if y < minY then y else minY)
      (if maxY < y then y else maxY)
  else (minX, minY, maxY)
termination_by limit.toNat - i.toNat

/-- Whether the cell with key `k` is in the 80 columns from `minX`. -/
@[inline]
def inLife105Block (minX : Int32) (k : UInt64) : Bool := ((cellKeyX k).toInt32 - minX).toUInt32 < 80

/-- Adds the cells `i` onward that are not in the 80 columns from `minX`. -/
def life105Rest (cells : Array UInt64) (minX : Int32) (i limit : UInt32) (acc : U64Buf) : U64Buf :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let k := cells[i.toNat]!
    life105Rest cells minX (i + 1) limit (if inLife105Block minX k then acc else U64Buf.push acc k)
  else acc
termination_by limit.toNat - i.toNat

/--
Appends lines `j` onward of `block`, and then the blocks of `cells`: the block of the 80 columns from the least x,
from the least to the greatest y of the cells, and then the blocks of the cells outside it. Each block has a cell,
so `fuel` blocks are enough for `fuel` cells.
-/
def serializeLife105.loop (fuel : UInt32) (cells : Array UInt64) (block : Array String) (j : UInt32)
    (acc : GrowBuf String) : GrowBuf String :=
  if hj : j < block.size.toUInt32 then
    have : block.size.toUInt32.toNat - (j + 1).toNat < block.size.toUInt32.toNat - j.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp hj
      have h2 : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt block.size.toUInt32
        simp only [UInt32.toNat_one]
        omega
      omega
    serializeLife105.loop fuel cells block (j + 1) (acc.push block[j.toNat]!)
  else if hf : fuel = 0 then acc
  else if cells.size.toUInt32 == 0 then acc
  else
    have : (fuel - 1).toNat < fuel.toNat := by
      have h1 : fuel.toNat ≠ 0 := fun h => hf (UInt32.toNat_inj.mp (by simpa using h))
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp; omega
    let k := cells[0]!
    let y := (cellKeyY k).toInt32
    let bounds := life105Bounds cells 1 cells.size.toUInt32 (cellKeyX k).toInt32 y y
    let minX := bounds.1
    let block := serializeLife105Block cells minX bounds.2.1 bounds.2.2
    let rest := U64Buf.toArray (life105Rest cells minX 0 cells.size.toUInt32 U64Buf.empty)
    serializeLife105.loop (fuel - 1) rest block 0 acc
termination_by (fuel.toNat, block.size.toUInt32.toNat - j.toNat)

/-- Serializes cells (as `cellBits`): the header lines and then blocks of 80 columns covering every cell. -/
@[export life105_serialize]
def serializeLife105 (cells : Array UInt64) : Array String :=
  (serializeLife105.loop cells.size.toUInt32 cells #[] 0 ((GrowBuf.empty.push "#Life 1.05").push "#N")).toArray

end Algorithm

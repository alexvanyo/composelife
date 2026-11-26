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
# Life 1.06

A `#Life 1.06` header line followed by one `x y` coordinate line per alive cell.
-/

/-- How deserialization ended. -/
@[kotlin_class "sealed class Life106Status"]
inductive Life106Status where
  | ok
  | emptyFile
  /-- The first line is not the `#Life 1.06` header. -/
  | invalidHeader (line : String)
  /-- Line `lineIndex` (1-based) is not a coordinate line. -/
  | invalidLine (lineIndex : UInt32) (line : String)
  deriving DecidableEq, Repr

@[kotlin_class "Life106Result"]
structure Life106Result where
  status : Life106Status
  /-- The keys (`cellBits`) of the cells. -/
  cells : Array UInt64
  deriving DecidableEq, Repr

/-- Parses an `x y` coordinate line. Surrounding spaces are allowed; out-of-range values are rejected. -/
def parseCoordLine (line : String) : Option (Int32 × Int32) :=
  let bytes := line.toByteArray
  let limit := bytes.size.toUInt32
  let p0 := skipSpaces bytes 0 limit
  match parseInt32At bytes p0 limit with
  | none => none
  | some r1 =>
    if r1.next < limit && isSpaceByte (bytes.get! r1.next.toNat) then
      let p1 := skipSpaces bytes r1.next limit
      match parseInt32At bytes p1 limit with
      | none => none
      | some r2 => if skipSpaces bytes r2.next limit == limit then some (r1.val, r2.val) else none
    else none

/-- Parses lines `i` onward as coordinate lines. -/
def deserializeLife106.loop (lines : Array String) (i : UInt32) (limit : UInt32)
    (acc : U64Buf) : Life106Result :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let line := lines[i.toNat]!
    match parseCoordLine line with
    | some coord => deserializeLife106.loop lines (i + 1) limit (U64Buf.push acc (cellBits coord))
    | none => ⟨.invalidLine (i + 1) line, noCells⟩
  else
    ⟨.ok, U64Buf.toArray acc⟩
termination_by limit.toNat - i.toNat

@[export life106_deserialize, kotlin_types "Array<String>" "_"]
def deserializeLife106 (lines : Array String) : Life106Result :=
  if lines.size.toUInt32 == 0 then
    ⟨.emptyFile, noCells⟩
  else
    let header := lines[0]!
    if header != "#Life 1.06" then
      ⟨.invalidHeader header, noCells⟩
    else
      deserializeLife106.loop lines 1 lines.size.toUInt32 U64Buf.empty

/-- The coordinate line for the cell at (`x`, `y`), given as the bits of the coordinates. -/
def formatCoordLine (x y : UInt32) : String := s!"{x.toInt32} {y.toInt32}"

/-- Appends the coordinate lines for cells (as `cellBits`) `i` onward. -/
def serializeLife106.loop (cells : Array UInt64) (i : UInt32) (limit : UInt32)
    (acc : GrowBuf String) : GrowBuf String :=
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
    serializeLife106.loop cells (i + 1) limit (acc.push (formatCoordLine (cellKeyX k) (cellKeyY k)))
  else
    acc
termination_by limit.toNat - i.toNat

/-- Serializes cells, given as `cellBits`. -/
@[export life106_serialize]
def serializeLife106 (cells : Array UInt64) : Array String :=
  (serializeLife106.loop cells 0 cells.size.toUInt32 (GrowBuf.empty.push "#Life 1.06")).toArray

end Algorithm

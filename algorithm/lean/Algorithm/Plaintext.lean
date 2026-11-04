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

import Lean.Compiler.Kotlin
import Init.Data.UInt

namespace Algorithm

@[kotlin_class "PlaintextWarning"]
structure PlaintextWarning where
  tag : UInt32
  lineIndex : UInt32
  columnIndex : UInt32
  charVal : UInt32
  deriving DecidableEq, Repr

@[kotlin_class "PlaintextResult"]
structure PlaintextResult where
  warnings : Array PlaintextWarning
  cells : Array (Int32 × Int32)
  deriving DecidableEq, Repr

def cellContains (cells : Array (Int32 × Int32)) (x y : Int32) : Bool :=
  let rec loop (i : UInt32) (limit : UInt32) : Bool :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (cx, cy) := cells[i.toNat]!
      if cx == x && cy == y then true
      else loop (i + 1) limit
    else false
  termination_by limit.toNat - i.toNat
  loop 0 cells.size.toUInt32

def parsePlaintextLine (lineBytes : ByteArray) (lineIdx rowIdx : UInt32)
    (warns : Array PlaintextWarning) (cells : Array (Int32 × Int32)) :
    Array PlaintextWarning × Array (Int32 × Int32) :=
  let rec loop (col : UInt32) (limit : UInt32) (warns : Array PlaintextWarning) (cells : Array (Int32 × Int32)) :
      Array PlaintextWarning × Array (Int32 × Int32) :=
    if h : col < limit then
      have : limit.toNat - (col + 1).toNat < limit.toNat - col.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (col + 1).toNat = col.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let b := lineBytes.get! col.toNat
      if b == 46 then -- '.'
        loop (col + 1) limit warns cells
      else if b == 79 then -- 'O'
        loop (col + 1) limit warns (cells.push (col.toInt32, rowIdx.toInt32))
      else
        let newWarns := warns.push ⟨2, lineIdx, col + 1, b.toUInt32⟩
        let newCells := if b == 32 then cells else cells.push (col.toInt32, rowIdx.toInt32)
        loop (col + 1) limit newWarns newCells
    else (warns, cells)
  termination_by limit.toNat - col.toNat
  loop 0 lineBytes.size.toUInt32 warns cells

@[export plaintext_deserialize]
def deserializePlaintext (lines : Array String) : PlaintextResult :=
  let rec loop (i : UInt32) (numLines : UInt32) (rowIdx : UInt32) (longestLineIdx longestLen : UInt32)
      (hasLongest : Bool) (warns : Array PlaintextWarning) (cells : Array (Int32 × Int32)) : PlaintextResult :=
    if h : i < numLines then
      have : numLines.toNat - (i + 1).toNat < numLines.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt numLines
          simp only [UInt32.toNat_one]
          omega
        omega
      let line := lines[i.toNat]!
      let bytes := line.toByteArray
      let len := bytes.size.toUInt32
      if len == 0 then
        let newWarns := if i + 1 < numLines then warns.push ⟨0, i + 1, 0, 0⟩ else warns
        loop (i + 1) numLines rowIdx longestLineIdx longestLen hasLongest newWarns cells
      else if bytes.get! 0 == 33 then -- '!'
        loop (i + 1) numLines rowIdx longestLineIdx longestLen hasLongest warns cells
      else
        let (curLongestIdx, curLongestLen, nextHasLongest, lenWarns) :=
          if !hasLongest then
            (i + 1, len, true, warns)
          else if len > longestLen then
            (i + 1, len, true, warns.push ⟨1, longestLineIdx, 0, 0⟩)
          else if len < longestLen then
            (longestLineIdx, longestLen, true, warns.push ⟨1, i + 1, 0, 0⟩)
          else
            (longestLineIdx, longestLen, true, warns)
        let (allWarns, allCells) := parsePlaintextLine bytes (i + 1) rowIdx lenWarns cells
        loop (i + 1) numLines (rowIdx + 1) curLongestIdx curLongestLen nextHasLongest allWarns allCells
    else ⟨warns, cells⟩
  termination_by numLines.toNat - i.toNat
  loop 0 lines.size.toUInt32 0 0 0 false #[] #[]

@[export plaintext_serialize]
def serializePlaintext (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32) : Array String :=
  if cells.size.toUInt32 == 0 then #["."]
  else
    let width : UInt32 := (maxX - minX + 1).toUInt32
    let height : UInt32 := (maxY - minY + 1).toUInt32
    let rec buildRow (y : Int32) (col : UInt32) (width : UInt32) (acc : String) : String :=
      if h : col < width then
        have : width.toNat - (col + 1).toNat < width.toNat - col.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (col + 1).toNat = col.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt width
            simp only [UInt32.toNat_one]
            omega
          omega
        let x := minX + col.toInt32
        let ch := if cellContains cells x y then "O" else "."
        buildRow y (col + 1) width (acc ++ ch)
      else acc
    termination_by width.toNat - col.toNat
    let rec buildRows (row : UInt32) (height : UInt32) (acc : Array String) : Array String :=
      if h : row < height then
        have : height.toNat - (row + 1).toNat < height.toNat - row.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (row + 1).toNat = row.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt height
            simp only [UInt32.toNat_one]
            omega
          omega
        let y := minY + row.toInt32
        let rowStr := buildRow y 0 width ""
        buildRows (row + 1) height (acc.push rowStr)
      else acc
    termination_by height.toNat - row.toNat
    buildRows 0 height #[]

end Algorithm

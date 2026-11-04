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

@[kotlin_class "Life105Warning"]
structure Life105Warning where
  tag : UInt32
  line : String
  lineIndex : UInt32
  columnIndex : UInt32
  deriving DecidableEq, Repr

@[kotlin_class "Life105Result"]
structure Life105Result where
  status : UInt32
  errLine : String
  errLineIndex : UInt32
  errColumnIndex : UInt32
  warnings : Array Life105Warning
  cells : Array (Int32 × Int32)
  deriving DecidableEq, Repr

@[kotlin_class "Life105BlockHeader"]
structure Life105BlockHeader where
  x : Int32
  y : Int32
  deriving DecidableEq, Repr

@[inline]
def isDigitByte (b : UInt8) : Bool := b >= 48 && b <= 57

structure Life105ParseIntResult where
  val : Int32
  nextPos : UInt32
  deriving DecidableEq, Repr

def parseSignedIntAt105 (bytes : ByteArray) (pos limit : UInt32) : Option Life105ParseIntResult :=
  if pos >= limit then none
  else
    let isNeg := bytes.get! pos.toNat == 45
    let startDigits := if isNeg then pos + 1 else pos
    if startDigits >= limit then none
    else
      let rec loop (p : UInt32) (limit : UInt32) (acc : UInt32) (hasDigits : Bool) : Option Life105ParseIntResult :=
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
          if isDigitByte b then
            loop (p + 1) limit (acc * 10 + (b.toUInt32 - 48)) true
          else if hasDigits then
            let v := if isNeg then (0 : Int32) - acc.toInt32 else acc.toInt32
            some ⟨v, p⟩
          else
            none
        else if hasDigits then
          let v := if isNeg then (0 : Int32) - acc.toInt32 else acc.toInt32
          some ⟨v, p⟩
        else
          none
      termination_by limit.toNat - p.toNat
      loop startDigits limit 0 false

def checkRuleLine (bytes : ByteArray) : UInt32 :=
  let limit := bytes.size.toUInt32
  if limit < 5 then 1
  else if bytes.get! 0 != 35 || bytes.get! 1 != 82 || bytes.get! 2 != 32 then 1 -- "#R "
  else
    let rec findSlash (p : UInt32) (limit : UInt32) : Option UInt32 :=
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
        if b == 47 then some p -- '/'
        else if isDigitByte b then findSlash (p + 1) limit
        else none
      else none
    termination_by limit.toNat - p.toNat
    match findSlash 3 limit with
    | none => 1
    | some slashPos =>
      if slashPos == 3 then 1 -- no survival digits
      else if slashPos + 1 >= limit then 1 -- no birth digits
      else
        let rec checkBirth (p : UInt32) (limit : UInt32) (allThree : Bool) : Bool :=
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
            if !isDigitByte b then false
            else checkBirth (p + 1) limit (allThree && b == 51)
          else allThree
        termination_by limit.toNat - p.toNat
        let rec checkSurvival (p : UInt32) (slashPos : UInt32) (hasTwo hasThree onlyTwoThree : Bool) :
            (Bool × Bool × Bool) :=
          if h : p < slashPos then
            have : slashPos.toNat - (p + 1).toNat < slashPos.toNat - p.toNat := by
              have h1 := UInt32.lt_iff_toNat_lt.mp h
              have h2 : (p + 1).toNat = p.toNat + 1 := by
                rw [UInt32.toNat_add]
                have := UInt32.toNat_lt slashPos
                simp only [UInt32.toNat_one]
                omega
              omega
            let b := bytes.get! p.toNat
            let isTwo := b == 50
            let isThree := b == 51
            checkSurvival (p + 1) slashPos (hasTwo || isTwo) (hasThree || isThree) (onlyTwoThree && (isTwo || isThree))
          else (hasTwo, hasThree, onlyTwoThree)
        termination_by slashPos.toNat - p.toNat
        let birthOk := checkBirth (slashPos + 1) limit true
        let (hasTwo, hasThree, onlyTwoThree) := checkSurvival 3 slashPos false false true
        if !birthOk then
          let rec allBirthDigits (p : UInt32) (limit : UInt32) : Bool :=
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
              if isDigitByte b then allBirthDigits (p + 1) limit else false
            else true
          termination_by limit.toNat - p.toNat
          if allBirthDigits (slashPos + 1) limit then 2 else 1
        else if hasTwo && hasThree && onlyTwoThree then 0
        else 2

def parseBlockHeader (bytes : ByteArray) : Option Life105BlockHeader :=
  let limit := bytes.size.toUInt32
  if limit < 5 then none
  else if bytes.get! 0 != 35 || bytes.get! 1 != 80 || bytes.get! 2 != 32 then none -- "#P "
  else
    match parseSignedIntAt105 bytes 3 limit with
    | none => none
    | some res1 =>
      if res1.nextPos >= limit || bytes.get! res1.nextPos.toNat != 32 then none
      else
        match parseSignedIntAt105 bytes (res1.nextPos + 1) limit with
        | none => none
        | some res2 =>
          if res2.nextPos == limit then some ⟨res1.val, res2.val⟩
          else none

def isRowLine (bytes : ByteArray) : Bool :=
  let limit := bytes.size.toUInt32
  if limit == 0 then false
  else
    let rec loop (p : UInt32) (limit : UInt32) : Bool :=
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
        if b == 46 || b == 42 then loop (p + 1) limit
        else false
      else true
    termination_by limit.toNat - p.toNat
    loop 0 limit

def addRowCells (bytes : ByteArray) (bx byCoord : Int32) (cells : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
  let limit := bytes.size.toUInt32
  let rec loop (col : UInt32) (limit : UInt32) (acc : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
    if h : col < limit then
      have : limit.toNat - (col + 1).toNat < limit.toNat - col.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (col + 1).toNat = col.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let b := bytes.get! col.toNat
      let newAcc := if b == 42 then acc.push (bx + col.toInt32, byCoord) else acc
      loop (col + 1) limit newAcc
    else acc
  termination_by limit.toNat - col.toNat
  loop 0 limit cells

def cellContains105 (cells : Array (Int32 × Int32)) (x y : Int32) : Bool :=
  let limit := cells.size.toUInt32
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
  loop 0 limit

@[export life105_deserialize]
def deserializeLife105 (lines : Array String) : Life105Result :=
  let numLines := lines.size.toUInt32
  if numLines == 0 then
    ⟨0, "", 0, 0, #[⟨0, "", 0, 0⟩], #[]⟩
  else
    let header := lines[0]!
    if header != "#Life 1.05" then
      ⟨1, header, 1, 0, #[], #[]⟩
    else
      let rec skipDesc (i : UInt32) (numLines : UInt32) : UInt32 :=
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
          if bytes.size >= 2 && bytes.get! 0 == 35 && bytes.get! 1 == 68 then
            skipDesc (i + 1) numLines
          else i
        else i
      termination_by numLines.toNat - i.toNat
      let lineAfterDescIdx := skipDesc 1 numLines
      let (hasErr, errRes, blockStartIdx, warns) :=
        if lineAfterDescIdx < numLines then
          let ruleLine := lines[lineAfterDescIdx.toNat]!
          let bytes := ruleLine.toByteArray
          if bytes.size >= 2 && bytes.get! 0 == 35 && bytes.get! 1 == 78 then -- "#N"
            let w := if ruleLine != "#N" then #[⟨1, ruleLine, lineAfterDescIdx + 1, 3⟩] else #[]
            (false, ⟨0, "", 0, 0, #[], #[]⟩, lineAfterDescIdx + 1, w)
          else if bytes.size >= 2 && bytes.get! 0 == 35 && bytes.get! 1 == 82 then -- "#R"
            match checkRuleLine bytes with
            | 0 => (false, ⟨0, "", 0, 0, #[], #[]⟩, lineAfterDescIdx + 1, #[])
            | 1 => (true, ⟨3, ruleLine, lineAfterDescIdx + 1, 3, #[], #[]⟩, 0, #[])
            | _ => (true, ⟨2, "", 0, 0, #[], #[]⟩, 0, #[])
          else
            (false, ⟨0, "", 0, 0, #[], #[]⟩, lineAfterDescIdx, #[])
        else
          (false, ⟨0, "", 0, 0, #[], #[]⟩, lineAfterDescIdx, #[])
      if hasErr then errRes
      else
        let rec parseBlocks (i : UInt32) (numLines : UInt32) (hasBlock : Bool) (blockX blockY : Int32)
            (rowIndex : Int32) (warns : Array Life105Warning) (cells : Array (Int32 × Int32)) : Life105Result :=
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
            if bytes.size >= 2 && bytes.get! 0 == 35 && bytes.get! 1 == 80 then -- starts with "#P"
              match parseBlockHeader bytes with
              | none => ⟨3, line, i + 1, 3, warns, cells⟩
              | some header => parseBlocks (i + 1) numLines true header.x header.y 0 warns cells
            else if isRowLine bytes then
              if !hasBlock then
                ⟨3, line, i + 1, 1, warns, cells⟩
              else
                let nextCells := addRowCells bytes blockX (blockY + rowIndex) cells
                parseBlocks (i + 1) numLines true blockX blockY (rowIndex + 1) warns nextCells
            else
              ⟨3, line, i + 1, 1, warns, cells⟩
          else
            ⟨0, "", 0, 0, warns, cells⟩
        termination_by numLines.toNat - i.toNat
        parseBlocks blockStartIdx numLines false 0 0 0 warns #[]

def buildLife105Row (cells : Array (Int32 × Int32)) (minX : Int32) (y : Int32) : String :=
  let rec loop (col : UInt32) (limit : UInt32) (acc : String) : String :=
    if h : col < limit then
      have : limit.toNat - (col + 1).toNat < limit.toNat - col.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (col + 1).toNat = col.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let x := minX + col.toInt32
      let ch := if cellContains105 cells x y then "*" else "."
      loop (col + 1) limit (acc ++ ch)
    else acc
  termination_by limit.toNat - col.toNat
  loop 0 80 ""

def buildLife105Rows (cells : Array (Int32 × Int32)) (minX minY maxY : Int32) (acc : Array String) : Array String :=
  let height : UInt32 := (maxY - minY + 1).toUInt32
  let rec loop (row : UInt32) (height : UInt32) (acc : Array String) : Array String :=
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
      loop (row + 1) height (acc.push (buildLife105Row cells minX y))
    else acc
  termination_by height.toNat - row.toNat
  loop 0 height acc

@[export life105_serialize_block]
def serializeLife105Block (cells : Array (Int32 × Int32)) (minX minY maxY : Int32) : Array String :=
  buildLife105Rows cells minX minY maxY #[]

end Algorithm

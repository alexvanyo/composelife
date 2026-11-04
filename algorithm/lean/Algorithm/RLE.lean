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

open Lean.Compiler.Kotlin

namespace Algorithm

@[kotlin_class "RLERunItem"]
structure RLERunItem where
  tag : UInt32 -- 0: RowEnd, 1: DeadRun, 2: AliveRun
  count : UInt32
  deriving DecidableEq, Repr

@[kotlin_class "RLEWarning"]
structure RLEWarning where
  tag : UInt32
  -- tag 0: UnexpectedEmptyFile
  -- tag 1: DuplicateTopLeftCoordinate
  -- tag 2: UnexpectedCharacter
  -- tag 3: UnexpectedInput
  lineIndex : UInt32
  columnIndex : UInt32
  charVal : UInt32
  strVal : String
  offsetX : Int32
  offsetY : Int32
  deriving DecidableEq, Repr

@[kotlin_class "RLEOffset"]
structure RLEOffset where
  offsetX : Int32
  offsetY : Int32
  deriving DecidableEq, Repr

@[kotlin_class "RLECommentResult"]
structure RLECommentResult where
  headerIdx : UInt32
  offsetX : Int32
  offsetY : Int32
  warnings : Array RLEWarning
  deriving DecidableEq, Repr

@[kotlin_class "RLECharsResult"]
structure RLECharsResult where
  curCount : UInt32
  hasCount : Bool
  finished : Bool
  runs : Array (UInt32 × UInt32)
  warnings : Array RLEWarning
  deriving DecidableEq, Repr

@[kotlin_class "RLELinesResult"]
structure RLELinesResult where
  runs : Array (UInt32 × UInt32)
  warnings : Array RLEWarning
  deriving DecidableEq, Repr

@[noinline]
def zeroOffset : Int32 := 0

@[kotlin_class "RLEResult"]
structure RLEResult where
  status : UInt32
  -- 0: Success
  -- 1: UnexpectedEmptyFile
  -- 2: UnexpectedHeader
  -- 3: RuleNotSupported
  errLine : String
  errLineIndex : UInt32
  warnings : Array RLEWarning
  cells : Array (Int32 × Int32)
  deriving DecidableEq, Repr

@[inline]
def isDigitByteRLE (b : UInt8) : Bool := b >= 48 && b <= 57

@[inline]
def isSpaceByteRLE (b : UInt8) : Bool := b == 32 || b == 9 || b == 13

structure RLEParseIntResult where
  val : Int32
  nextPos : UInt32
  deriving DecidableEq, Repr

def parseSignedIntAtRLE (bytes : ByteArray) (pos limit : UInt32) : Option RLEParseIntResult :=
  if pos >= limit then none
  else
    let isNeg := bytes.get! pos.toNat == 45
    let startDigits := if isNeg then pos + 1 else pos
    if startDigits >= limit then none
    else
      let rec loop (p : UInt32) (acc : UInt32) (hasDigits : Bool) : Option RLEParseIntResult :=
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
          if isDigitByteRLE b then
            loop (p + 1) (acc * 10 + (b.toUInt32 - 48)) true
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
      loop startDigits 0 false

def skipSpacesRLE (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  if h : pos < limit then
    have : limit.toNat - (pos + 1).toNat < limit.toNat - pos.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    if isSpaceByteRLE (bytes.get! pos.toNat) then
      skipSpacesRLE bytes (pos + 1) limit
    else
      pos
  else
    pos
termination_by limit.toNat - pos.toNat

def parseRLEOffset (bytes : ByteArray) : Option RLEOffset :=
  let limit := bytes.size.toUInt32
  if limit < 4 then none
  else if bytes.get! 0 == 35 && (bytes.get! 1 == 82 || bytes.get! 1 == 80) && bytes.get! 2 == 32 then
    let p0 := skipSpacesRLE bytes 3 limit
    match parseSignedIntAtRLE bytes p0 limit with
    | none => none
    | some res1 =>
      let p1 := skipSpacesRLE bytes res1.nextPos limit
      match parseSignedIntAtRLE bytes p1 limit with
      | none => none
      | some res2 => some ⟨res1.val, res2.val⟩
  else none

def cellContainsRLE (cells : Array (Int32 × Int32)) (x y : Int32) : Bool :=
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

def rleCombine (items : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
  let limit := items.size.toUInt32
  if limit == 0 then #[]
  else
    let (firstChar, firstCount) := items[0]!
    let rec loop (i : UInt32) (limit : UInt32) (curChar : UInt8) (curCount : UInt32)
        (acc : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
      if h : i < limit then
        have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let (ch, cnt) := items[i.toNat]!
        if ch == curChar then
          loop (i + 1) limit curChar (curCount + cnt) acc
        else
          loop (i + 1) limit ch cnt (acc.push (curChar, curCount))
      else acc.push (curChar, curCount)
    termination_by limit.toNat - i.toNat
    loop 1 limit firstChar firstCount #[]

def trimTrailingDead (items : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
  let limit := items.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) (acc : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (ch, cnt) := items[i.toNat]!
      if i + 1 < limit then
        let (nextCh, _) := items[(i + 1).toNat]!
        if ch == 98 && (nextCh == 36 || nextCh == 33) then -- 'b' before '$' or '!'
          loop (i + 1) limit acc
        else
          loop (i + 1) limit (acc.push (ch, cnt))
      else
        loop (i + 1) limit (acc.push (ch, cnt))
    else acc
  termination_by limit.toNat - i.toNat
  loop 0 limit #[]

def formatRLEItem (ch : UInt8) (cnt : UInt32) : String :=
  let tagStr := if ch == 111 then "o" else if ch == 98 then "b" else if ch == 36 then "$" else "!"
  if cnt == 1 then tagStr
  else s!"{cnt}{tagStr}"

def wrapRLELines (items : Array String) : Array String :=
  let limit := items.size.toUInt32
  if limit == 0 then #[]
  else
    let rec loop (i : UInt32) (limit : UInt32) (curLine : String) (acc : Array String) : Array String :=
      if h : i < limit then
        have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let item := items[i.toNat]!
        if curLine.length.toUInt32 + item.length.toUInt32 > (70 : UInt32) then
          loop (i + 1) limit item (acc.push curLine)
        else
          loop (i + 1) limit (curLine ++ item) acc
      else if curLine.length.toUInt32 > (0 : UInt32) then acc.push curLine
      else acc
    termination_by limit.toNat - i.toNat
    loop 0 limit "" #[]

def buildRawTags (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32) : Array (UInt8 × UInt32) :=
  let width : UInt32 := (maxX - minX + 1).toUInt32
  let height : UInt32 := (maxY - minY + 1).toUInt32
  let rec loopRow (row : UInt32) (height : UInt32) (acc : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
    if hr : row < height then
      have : height.toNat - (row + 1).toNat < height.toNat - row.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp hr
        have h2 : (row + 1).toNat = row.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt height
          simp only [UInt32.toNat_one]
          omega
        omega
      let y := minY + row.toInt32
      let rec loopCol (col : UInt32) (width : UInt32) (rowAcc : Array (UInt8 × UInt32)) : Array (UInt8 × UInt32) :=
        if hc : col < width then
          have : width.toNat - (col + 1).toNat < width.toNat - col.toNat := by
            have h1 := UInt32.lt_iff_toNat_lt.mp hc
            have h2 : (col + 1).toNat = col.toNat + 1 := by
              rw [UInt32.toNat_add]
              have := UInt32.toNat_lt width
              simp only [UInt32.toNat_one]
              omega
            omega
          let x := minX + col.toInt32
          let tag : UInt8 := if cellContainsRLE cells x y then 111 else 98
          loopCol (col + 1) width (rowAcc.push (tag, 1))
        else rowAcc
      termination_by width.toNat - col.toNat
      let rowTags := loopCol 0 width acc
      let rowTagsWithEnd := if row + 1 < height then rowTags.push (36, 1) else rowTags
      loopRow (row + 1) height rowTagsWithEnd
    else acc.push (33, 1)
  termination_by height.toNat - row.toNat
  loopRow 0 height #[]

@[export rle_serialize]
def serializeRLE (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32) : Array String :=
  if cells.size == 0 then
    #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"]
  else
    let width : UInt32 := (maxX - minX + 1).toUInt32
    let height : UInt32 := (maxY - minY + 1).toUInt32
    let rawTags := buildRawTags cells minX maxX minY maxY
    let rle1 := rleCombine rawTags
    let trimmed := trimTrailingDead rle1
    let rle2 := rleCombine trimmed
    let rec formatLoop (i : UInt32) (limit : UInt32) (acc : Array String) : Array String :=
      if h : i < limit then
        have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        let (ch, cnt) := rle2[i.toNat]!
        formatLoop (i + 1) limit (acc.push (formatRLEItem ch cnt))
      else acc
    termination_by limit.toNat - i.toNat
    let formatted := formatLoop 0 rle2.size.toUInt32 #[]
    let wrapped := wrapRLELines formatted
    let header1 := s!"#R {minX} {minY}"
    let header2 := s!"x = {width}, y = {height}, rule = B3/S23"
    let rec prependHeaders (i : UInt32) (limit : UInt32) (acc : Array String) : Array String :=
      if h : i < limit then
        have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        prependHeaders (i + 1) limit (acc.push wrapped[i.toNat]!)
      else acc
    termination_by limit.toNat - i.toNat
    prependHeaders 0 wrapped.size.toUInt32 #[header1, header2]

@[export rle_decode_runs]
def decodeRLERuns (runs : Array (UInt32 × UInt32)) (startX startY : Int32) : Array (Int32 × Int32) :=
  let limit := runs.size.toUInt32
  let rec loop (i : UInt32) (limit : UInt32) (x y : Int32) (acc : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
    if h : i < limit then
      have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
        have h1 := UInt32.lt_iff_toNat_lt.mp h
        have h2 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add]
          have := UInt32.toNat_lt limit
          simp only [UInt32.toNat_one]
          omega
        omega
      let (tag, count) := runs[i.toNat]!
      if tag == 0 then -- RowEnd
        loop (i + 1) limit startX (y + count.toInt32) acc
      else if tag == 1 then -- DeadRun
        loop (i + 1) limit (x + count.toInt32) y acc
      else -- AliveRun
        let rec addCells (k : UInt32) (kLimit : UInt32) (cellsAcc : Array (Int32 × Int32)) : Array (Int32 × Int32) :=
          if hk : k < kLimit then
            have : kLimit.toNat - (k + 1).toNat < kLimit.toNat - k.toNat := by
              have h1 := UInt32.lt_iff_toNat_lt.mp hk
              have h2 : (k + 1).toNat = k.toNat + 1 := by
                rw [UInt32.toNat_add]
                have := UInt32.toNat_lt kLimit
                simp only [UInt32.toNat_one]
                omega
              omega
            addCells (k + 1) kLimit (cellsAcc.push (x + k.toInt32, y))
          else cellsAcc
        termination_by kLimit.toNat - k.toNat
        let nextAcc := addCells 0 count acc
        loop (i + 1) limit (x + count.toInt32) y nextAcc
    else acc
  termination_by limit.toNat - i.toNat
  loop 0 limit startX startY #[]

def checkRLEHeaderRule (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  let p0 := skipSpacesRLE bytes pos limit
  if p0 >= limit then 0 -- default Conway
  else if bytes.get! p0.toNat != 44 then 2 -- expected ','
  else
    let p1 := skipSpacesRLE bytes (p0 + 1) limit
    if p1 + 4 <= limit &&
       (bytes.get! p1.toNat == 114 || bytes.get! p1.toNat == 82) && -- 'r' / 'R'
       (bytes.get! (p1 + 1).toNat == 117 || bytes.get! (p1 + 1).toNat == 85) && -- 'u' / 'U'
       (bytes.get! (p1 + 2).toNat == 108 || bytes.get! (p1 + 2).toNat == 76) && -- 'l' / 'L'
       (bytes.get! (p1 + 3).toNat == 101 || bytes.get! (p1 + 3).toNat == 69) then -- 'e' / 'E'
      let p2 := skipSpacesRLE bytes (p1 + 4) limit
      if p2 < limit && bytes.get! p2.toNat == 61 then -- '='
        let p3 := skipSpacesRLE bytes (p2 + 1) limit
        -- Check "B3/S23" (or "b3/s23")
        if p3 + 6 <= limit &&
           (bytes.get! p3.toNat == 66 || bytes.get! p3.toNat == 98) &&
           bytes.get! (p3 + 1).toNat == 51 &&
           bytes.get! (p3 + 2).toNat == 47 &&
           (bytes.get! (p3 + 3).toNat == 83 || bytes.get! (p3 + 3).toNat == 115) &&
           bytes.get! (p3 + 4).toNat == 50 &&
           bytes.get! (p3 + 5).toNat == 51 &&
           skipSpacesRLE bytes (p3 + 6) limit == limit then 0
        -- Check "23/3"
        else if p3 + 4 <= limit &&
           bytes.get! p3.toNat == 50 &&
           bytes.get! (p3 + 1).toNat == 51 &&
           bytes.get! (p3 + 2).toNat == 47 &&
           bytes.get! (p3 + 3).toNat == 51 &&
           skipSpacesRLE bytes (p3 + 4) limit == limit then 0
        else 3 -- unsupported rule
      else 2 -- expected '='
    else 2 -- expected "rule"

def parseRLEHeader (bytes : ByteArray) : UInt32 :=
  let limit := bytes.size.toUInt32
  let p0 := skipSpacesRLE bytes 0 limit
  if p0 >= limit || bytes.get! p0.toNat != 120 then 2 -- 'x'
  else
    let p1 := skipSpacesRLE bytes (p0 + 1) limit
    if p1 >= limit || bytes.get! p1.toNat != 61 then 2 -- '='
    else
      let p2 := skipSpacesRLE bytes (p1 + 1) limit
      match parseSignedIntAtRLE bytes p2 limit with
      | none => 2
      | some resX =>
        let p3 := skipSpacesRLE bytes resX.nextPos limit
        if p3 >= limit || bytes.get! p3.toNat != 44 then 2 -- ','
        else
          let p4 := skipSpacesRLE bytes (p3 + 1) limit
          if p4 >= limit || bytes.get! p4.toNat != 121 then 2 -- 'y'
          else
            let p5 := skipSpacesRLE bytes (p4 + 1) limit
            if p5 >= limit || bytes.get! p5.toNat != 61 then 2 -- '='
            else
              let p6 := skipSpacesRLE bytes (p5 + 1) limit
              match parseSignedIntAtRLE bytes p6 limit with
              | none => 2
              | some resY =>
                checkRLEHeaderRule bytes resY.nextPos limit

def natDigitCount (n : UInt32) : UInt32 :=
  if n < 10 then 1
  else if n < 100 then 2
  else if n < 1000 then 3
  else if n < 10000 then 4
  else if n < 100000 then 5
  else if n < 1000000 then 6
  else if n < 10000000 then 7
  else if n < 100000000 then 8
  else if n < 1000000000 then 9
  else 10

@[export rle_deserialize]
def deserializeRLE (lines : Array String) : RLEResult :=
  let numLines := lines.size.toUInt32
  if numLines == 0 then
    ⟨1, "", 0, #[⟨0, 0, 0, 0, "", zeroOffset, zeroOffset⟩], #[]⟩
  else
    let rec parseComments (i : UInt32) (numLines : UInt32) (offsetX offsetY : Int32) (hasOffset : Bool)
        (warns : Array RLEWarning) : Option RLECommentResult :=
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
        if bytes.size.toUInt32 > 0 && bytes.get! 0 == 35 then -- '#'
          match parseRLEOffset bytes with
          | some off =>
            let newWarns := if hasOffset then warns.push ⟨1, i + 1, 0, 0, "", off.offsetX, off.offsetY⟩ else warns
            parseComments (i + 1) numLines off.offsetX off.offsetY true newWarns
          | none =>
            parseComments (i + 1) numLines offsetX offsetY hasOffset warns
        else
          some ⟨i, offsetX, offsetY, warns⟩
      else none
    termination_by numLines.toNat - i.toNat
    match parseComments 0 numLines 0 0 false #[] with
    | none => ⟨2, "none", numLines, #[], #[]⟩
    | some commRes =>
      let headerLine := lines[commRes.headerIdx.toNat]!
      let headerStatus := parseRLEHeader headerLine.toByteArray
      if headerStatus != 0 then
        ⟨headerStatus, headerLine, commRes.headerIdx + 1, commRes.warnings, #[]⟩
      else
        let rec parseLines (lineIdx : UInt32) (numLines : UInt32) (curCount : UInt32) (hasCount : Bool)
            (finished : Bool) (runs : Array (UInt32 × UInt32)) (warns : Array RLEWarning) :
            RLELinesResult :=
          if hl : lineIdx < numLines then
            have : numLines.toNat - (lineIdx + 1).toNat < numLines.toNat - lineIdx.toNat := by
              have h1 := UInt32.lt_iff_toNat_lt.mp hl
              have h2 : (lineIdx + 1).toNat = lineIdx.toNat + 1 := by
                rw [UInt32.toNat_add]
                have := UInt32.toNat_lt numLines
                simp only [UInt32.toNat_one]
                omega
              omega
            let line := lines[lineIdx.toNat]!
            let bytes := line.toByteArray
            let lineLen := bytes.size.toUInt32
            let rec parseChars (col : UInt32) (lineLen : UInt32) (curCount : UInt32) (hasCount : Bool)
                (runs : Array (UInt32 × UInt32)) (warns : Array RLEWarning) :
                RLECharsResult :=
              if hc : col < lineLen then
                have : lineLen.toNat - (col + 1).toNat < lineLen.toNat - col.toNat := by
                  have h1 := UInt32.lt_iff_toNat_lt.mp hc
                  have h2 : (col + 1).toNat = col.toNat + 1 := by
                    rw [UInt32.toNat_add]
                    have := UInt32.toNat_lt lineLen
                    simp only [UInt32.toNat_one]
                    omega
                  omega
                let b := bytes.get! col.toNat
                if isDigitByteRLE b then
                  let newCount := curCount * 10 + (b.toUInt32 - 48)
                  parseChars (col + 1) lineLen newCount true runs warns
                else if b == 36 then -- '$'
                  let count := if hasCount then curCount else 1
                  let newRuns := runs.push (0, count)
                  parseChars (col + 1) lineLen 0 false newRuns warns
                else if b == 33 then -- '!'
                  let newRuns := runs.push (0, 1)
                  let countWarns :=
                    if hasCount then
                      let countLen := natDigitCount curCount
                      warns.push ⟨3, lineIdx + 1, col + 1 - countLen, 0, s!"{curCount}!", zeroOffset, zeroOffset⟩
                    else warns
                  let finalWarns :=
                    if col + 1 < lineLen then
                      countWarns.push ⟨4, lineIdx + 1, col + 2, (bytes.get! (col + 1).toNat).toUInt32, "", zeroOffset, zeroOffset⟩
                    else if lineIdx + 1 < numLines then
                      countWarns.push ⟨3, lineIdx + 2, 1, 0, lines[(lineIdx + 1).toNat]!, zeroOffset, zeroOffset⟩
                    else countWarns
                  ⟨0, false, true, newRuns, finalWarns⟩
                else if b == 98 then -- 'b'
                  let count := if hasCount then curCount else 1
                  let newRuns := runs.push (1, count)
                  parseChars (col + 1) lineLen 0 false newRuns warns
                else if isSpaceByteRLE b then
                  parseChars (col + 1) lineLen curCount hasCount runs warns
                else -- alive cell 'o' or unrecognized
                  let newWarns :=
                    if b != 111 then
                      warns.push ⟨2, lineIdx + 1, col + 1, b.toUInt32, "", zeroOffset, zeroOffset⟩
                    else warns
                  let count := if hasCount then curCount else 1
                  let newRuns := runs.push (2, count)
                  parseChars (col + 1) lineLen 0 false newRuns newWarns
              else ⟨curCount, hasCount, false, runs, warns⟩
            termination_by lineLen.toNat - col.toNat
            let charRes := parseChars 0 lineLen curCount hasCount runs warns
            if charRes.finished then
              ⟨charRes.runs, charRes.warnings⟩
            else
              parseLines (lineIdx + 1) numLines charRes.curCount charRes.hasCount false charRes.runs charRes.warnings
          else ⟨runs, warns⟩
        termination_by numLines.toNat - lineIdx.toNat
        let linesRes := parseLines (commRes.headerIdx + 1) numLines 0 false false #[] commRes.warnings
        let cells := decodeRLERuns linesRes.runs commRes.offsetX commRes.offsetY
        ⟨0, "", 0, linesRes.warnings, cells⟩

end Algorithm

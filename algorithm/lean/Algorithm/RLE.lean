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
# Run Length Encoded (RLE)

`#` comment lines (`#R x y` or `#P x y` give the top-left coordinate), an `x = w, y = h, rule = ...` header, and
the pattern: runs `<count><tag>` with tags `b` (dead), `o` (alive) and `$` (end of row), ended by `!`. A count
applies to the tag right after it on the same line. Whitespace is ignored.
-/

@[kotlin_class "RLEWarning"]
structure RLEWarning where
  /--
  0: unexpected empty file, 1: duplicate top-left coordinate, 2: unexpected character, 3: unexpected input
  (`strVal`), 4: unexpected character after `!`.
  -/
  tag : UInt32
  lineIndex : UInt32
  columnIndex : UInt32
  charVal : UInt32
  strVal : String
  offsetX : Int32
  offsetY : Int32
  deriving DecidableEq, Repr

@[kotlin_class "RLEResult"]
structure RLEResult where
  /-- 0: success, 1: unexpected empty file, 2: unexpected header, 3: rule not supported, 4: unexpected input. -/
  status : UInt32
  errLine : String
  errLineIndex : UInt32
  errColumnIndex : UInt32
  warnings : Array RLEWarning
  /-- The keys (`cellBits`) of the cells. -/
  cells : Array UInt64
  deriving DecidableEq, Repr

/-- Zero, for the offset of warnings without one. Not inlined, as the Kotlin backend emits an `Int32` literal
in a constructor as unsigned. -/
@[noinline]
def zeroOffset : Int32 := 0

/-- Parses a `#R x y` or `#P x y` top-left coordinate line. -/
def parseRLEOffset (bytes : ByteArray) : Option ParsedCoords :=
  let limit := bytes.size.toUInt32
  if limit < 3 || bytes.get! 0 != 35 || (bytes.get! 1 != 82 && bytes.get! 1 != 80) || bytes.get! 2 != 32 then none
  else
    match parseInt32At bytes 3 limit with
    | none => none
    | some r1 =>
      if r1.next < limit && bytes.get! r1.next.toNat == 32 then
        match parseInt32At bytes (r1.next + 1) limit with
        | none => none
        | some r2 => if r2.next == limit then some ⟨r1.val, r2.val⟩ else none
      else none

/-- Whether `b` is `c` in either case, for an ASCII letter `c`. -/
@[inline]
def isLetterByte (b : UInt8) (c : UInt8) : Bool := b == c || b == c - 32

/--
Checks the rule after `rule =`: 0 for Conway's rules (birth digits {3}, survival digits {2, 3}, in any order and
with repeats), 2 if it is malformed and 3 for any other rule. The rule is `B<birth>/S<survival>` or
`<survival>/<birth>`.
-/
def checkRLERule (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  let p0 := skipSpaces bytes pos limit
  let hasLetters := p0 < limit && isLetterByte (bytes.get! p0.toNat) 98
  let s1 := if hasLetters then p0 + 1 else p0
  let (e1, first) := scanDigitSet bytes limit s1 0
  if e1 == s1 || !(e1 < limit) || bytes.get! e1.toNat != 47 then 2 -- '/'
  else
    let lettersOk := !hasLetters || (e1 + 1 < limit && isLetterByte (bytes.get! (e1 + 1).toNat) 115)
    if !lettersOk then 2
    else
      let s2 := if hasLetters then e1 + 2 else e1 + 1
      let (e2, second) := scanDigitSet bytes limit s2 0
      if e2 == s2 || skipSpaces bytes e2 limit != limit then 2
      else
        let (birth, survival) := if hasLetters then (first, second) else (second, first)
        if birth == birth3Mask && survival == survival23Mask then 0 else 3

/--
Checks an `x = w, y = h[, rule = r]` header line: 0 if it is valid with Conway's rules, 2 if it is malformed and 3
for another rule. Spaces around the parts are allowed.
-/
def parseRLEHeader (bytes : ByteArray) : UInt32 :=
  let limit := bytes.size.toUInt32
  let expect (p : UInt32) (c : UInt8) : Option UInt32 :=
    let q := skipSpaces bytes p limit
    if q < limit && bytes.get! q.toNat == c then some (q + 1) else none
  let expectNum (p : UInt32) : Option UInt32 :=
    match parseUInt32At bytes (skipSpaces bytes p limit) limit with
    | some r => some r.next
    | none => none
  match expect 0 120 >>= (expect · 61) >>= expectNum >>= (expect · 44) >>= (expect · 121) >>= (expect · 61)
      >>= expectNum with -- "x = w, y = h"
  | none => 2
  | some p =>
    let q := skipSpaces bytes p limit
    if q == limit then 0
    else
      match expect q 44 with -- ','
      | none => 2
      | some p1 =>
        let r := skipSpaces bytes p1 limit
        if r + 4 <= limit && limit - r >= 4 && isLetterByte (bytes.get! r.toNat) 114 &&
            isLetterByte (bytes.get! (r + 1).toNat) 117 && isLetterByte (bytes.get! (r + 2).toNat) 108 &&
            isLetterByte (bytes.get! (r + 3).toNat) 101 then -- "rule"
          match expect (r + 4) 61 with -- '='
          | none => 2
          | some p2 => checkRLERule bytes p2 limit
        else 2

/-- Copies the ASCII bytes among `bytes[s + k]` for `k` from `k` until `n` into `g`. -/
def copyAscii (bytes : ByteArray) (s n : UInt32) (k : UInt32) (g : AsciiBytes) : AsciiBytes :=
  if h : k < n then
    have : n.toNat - (k + 1).toNat < n.toNat - k.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt n
        simp only [UInt32.toNat_one]
        omega
      omega
    let b := bytes.get! (s + k).toNat
    copyAscii bytes s n (k + 1) (if hb : b < 128 then g.set k b hb else g)
  else g
termination_by n.toNat - k.toNat

/-- The bytes `s` until `e` as a string, with any byte that isn't ASCII replaced by `?`. -/
def asciiStringLossy (bytes : ByteArray) (s e : UInt32) : String :=
  let n := e - s
  (copyAscii bytes s n 0 (AsciiBytes.replicate n 63 (by decide))).toStringRange 0 n

/-- The largest run count. -/
def maxRunCount : UInt64 := 2147483647

/-- Adds the cells of alive runs `j` onward (with `k` cells of run `j` done). Runs are `(tag, count)` with tag 0
for an end of row, 1 for dead cells and 2 for alive cells. -/
def expandRuns (runs : Array (UInt32 × UInt32)) (numRuns : UInt32) (j k : UInt32) (x y startX : Int32)
    (cells : U64Buf) : U64Buf :=
  if hj : j < numRuns then
    have hk0 := UInt32.toNat_lt k
    have hnext : (numRuns.toNat - (j + 1).toNat) * 2 ^ 33 + (2 ^ 32 - (0 : UInt32).toNat) <
        (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) := by
      have hj1 := UInt32.lt_iff_toNat_lt.mp hj
      have hj2 : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt32.toNat_add]; have := UInt32.toNat_lt numRuns; simp only [UInt32.toNat_one]; omega
      rw [hj2, UInt32.toNat_zero]
      have : numRuns.toNat - j.toNat = (numRuns.toNat - (j.toNat + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
    match runs[j.toNat]! with
    | (tag, count) =>
      if tag == 2 then
        if hk : k < count then
          have : (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - (k + 1).toNat) <
              (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) := by
            have hk1 := UInt32.lt_iff_toNat_lt.mp hk
            have hc := UInt32.toNat_lt count
            have hk2 : (k + 1).toNat = k.toNat + 1 := by
              rw [UInt32.toNat_add, UInt32.toNat_one]; omega
            rw [hk2]
            apply Nat.add_lt_add_left
            omega
          expandRuns runs numRuns j (k + 1) x y startX (U64Buf.push cells (cellBits (x + k.toInt32, y)))
        else
          expandRuns runs numRuns (j + 1) 0 (x + count.toInt32) y startX cells
      else if tag == 1 then
        expandRuns runs numRuns (j + 1) 0 (x + count.toInt32) y startX cells
      else
        expandRuns runs numRuns (j + 1) 0 startX (y + count.toInt32) startX cells
  else cells
termination_by (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat)
decreasing_by all_goals first | exact this | exact hnext

/-- The successful result for the runs read so far. -/
def finishRLE (warns : GrowBuf RLEWarning) (runs : GrowBuf (UInt32 × UInt32)) (startX startY : Int32) : RLEResult :=
  let runArr := runs.toArray
  ⟨0, "", 0, 0, warns.toArray,
    U64Buf.toArray (expandRuns runArr runArr.size.toUInt32 0 0 startX startY startX U64Buf.empty)⟩

/--
Reads the pattern from line `i` on. In a line (`inLine`), `bytes` is the line, `p` the byte position and `col`
the character position; `count` is the pending run count, which started at byte `countP` (character
`countCol`).
-/
def parseRLEData (lines : Array String) (numLines : UInt32) (i : UInt32) (inLine : Bool) (bytes : ByteArray)
    (limit p col : UInt32) (count : UInt64) (hasCount : Bool) (countP countCol : UInt32)
    (warns : GrowBuf RLEWarning) (runs : GrowBuf (UInt32 × UInt32)) (startX startY : Int32) : RLEResult :=
  if hi : i < numLines then
    have hi1 : numLines.toNat - (i + 1).toNat < numLines.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp hi
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt numLines
        simp only [UInt32.toNat_one]
        omega
      omega
    if inLine then
      if hp : p < limit then
        let r := decodeCharAt bytes p limit
        have := decodeCharAt_next bytes p limit hp
        let cp := r.1
        if cp >= 48 && cp <= 57 then -- digit
          let newCount := if count > 4294967296 then count else count * 10 + (cp.toUInt64 - 48)
          parseRLEData lines numLines i true bytes limit r.2 (col + 1) newCount true
            (if hasCount then countP else p) (if hasCount then countCol else col) warns runs startX startY
        else if cp == 33 then -- '!'
          let warns := if hasCount then
              warns.push ⟨3, i + 1, countCol + 1, 0, asciiStringLossy bytes countP r.2, zeroOffset, zeroOffset⟩
            else warns
          let warns := if r.2 < limit then
              warns.push ⟨4, i + 1, col + 2, (decodeCharAt bytes r.2 limit).1, "", zeroOffset, zeroOffset⟩
            else if i + 1 < numLines then
              warns.push ⟨3, i + 2, 1, 0, lines[(i + 1).toNat]!, zeroOffset, zeroOffset⟩
            else warns
          finishRLE warns (runs.push (0, 1)) startX startY
        else if cp == 32 || cp == 9 || cp == 13 then -- whitespace
          parseRLEData lines numLines i true bytes limit r.2 (col + 1) count hasCount countP countCol warns runs
            startX startY
        else if hasCount && count > maxRunCount then
          ⟨4, asciiStringLossy bytes countP p, i + 1, countCol + 1, #[], noCells⟩
        else
          let n : UInt32 := if hasCount then count.toUInt32 else 1
          -- '$' ends rows, 'b' is dead, and anything else is alive, with a warning unless it is 'o'.
          let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
          let warns := if tag == 2 && cp != 111 then
              warns.push ⟨2, i + 1, col + 1, cp, "", zeroOffset, zeroOffset⟩
            else warns
          parseRLEData lines numLines i true bytes limit r.2 (col + 1) 0 false 0 0 warns (runs.push (tag, n))
            startX startY
      else
        -- A count at the end of a line is dropped.
        parseRLEData lines numLines (i + 1) false bytes limit 0 0 0 false 0 0 warns runs startX startY
    else
      let bytes := lines[i.toNat]!.toByteArray
      parseRLEData lines numLines i true bytes bytes.size.toUInt32 0 0 0 false 0 0 warns runs startX startY
  else finishRLE warns runs startX startY
termination_by (numLines.toNat - i.toNat) * 2 ^ 33 + (if inLine then limit.toNat - p.toNat else 2 ^ 32)
decreasing_by
  all_goals
    simp_all only [ite_true, Bool.false_eq_true, ite_false]
    first
      | omega
      | (have := UInt32.toNat_lt limit; omega)
      | (have := UInt32.toNat_lt (ByteArray.size lines[i.toNat]!.toByteArray).toUInt32; omega)

/-- Reads the comment lines from `i` on, then the header and the pattern. -/
def parseRLEComments (lines : Array String) (numLines : UInt32) (i : UInt32) (offsetX offsetY : Int32)
    (hasOffset : Bool) (warns : GrowBuf RLEWarning) : RLEResult :=
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
    if bytes.size.toUInt32 != 0 && bytes.get! 0 == 35 then -- '#'
      match parseRLEOffset bytes with
      | some c =>
        let warns := if hasOffset then warns.push ⟨1, i + 1, 0, 0, "", c.x, c.y⟩ else warns
        parseRLEComments lines numLines (i + 1) c.x c.y true warns
      | none => parseRLEComments lines numLines (i + 1) offsetX offsetY hasOffset warns
    else
      let status := parseRLEHeader bytes
      if status != 0 then ⟨status, line, i + 1, 0, warns.toArray, noCells⟩
      else
        parseRLEData lines numLines (i + 1) false bytes 0 0 0 0 false 0 0 warns GrowBuf.empty offsetX offsetY
  else ⟨2, "none", numLines, 0, warns.toArray, noCells⟩
termination_by numLines.toNat - i.toNat

@[export rle_deserialize, kotlin_types "Array<String>" "_"]
def deserializeRLE (lines : Array String) : RLEResult :=
  if lines.size.toUInt32 == 0 then
    ⟨1, "", 0, 0, #[⟨0, 0, 0, 0, "", zeroOffset, zeroOffset⟩], noCells⟩
  else
    parseRLEComments lines lines.size.toUInt32 0 0 0 false GrowBuf.empty

/-- The tags of runs. -/
def rleDead : UInt8 := 98
def rleAlive : UInt8 := 111
def rleRowEnd : UInt8 := 36
def rleEnd : UInt8 := 33

/--
Turns grid cells `k` onward (row `k / w`, column `k % w`) into run items `(tag, count)`, merging runs of the same
tag. Dead runs at the end of a row are dropped, and consecutive ends of rows are merged. `runTag` and `runLen`
are the current run (`runLen = 0` for none), and `rowEnds` the pending ends of rows, emitted before the next run.
-/
def gridItems (g : AsciiBytes) (w total : UInt32) (k : UInt32) (runTag : UInt8) (runLen : UInt32)
    (rowEnds : UInt32) (items : GrowBuf (UInt8 × UInt32)) : GrowBuf (UInt8 × UInt32) :=
  if h : k < total then
    have : total.toNat - (k + 1).toNat < total.toNat - k.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt total
        simp only [UInt32.toNat_one]
        omega
      omega
    let tag := g.1.get! k.toNat
    let grows := runLen != 0 && tag == runTag
    -- A run that ends before the end of the row is emitted, after any pending ends of rows.
    let flush := runLen != 0 && !grows
    let items := if flush && rowEnds != 0 then items.push (rleRowEnd, rowEnds) else items
    let items := if flush then items.push (runTag, runLen) else items
    let rowEnds := if flush then 0 else rowEnds
    let curTag := if grows then runTag else tag
    let curLen := if grows then runLen + 1 else 1
    if (k + 1) % w == 0 then
      -- The run ends with the row; a dead run there is dropped.
      let emit := curTag == rleAlive
      let items := if emit && rowEnds != 0 then items.push (rleRowEnd, rowEnds) else items
      let items := if emit then items.push (rleAlive, curLen) else items
      let rowEnds := if emit then 0 else rowEnds
      -- The end of this row is pending; one after the last row is never emitted.
      gridItems g w total (k + 1) rleDead 0 (rowEnds + 1) items
    else
      gridItems g w total (k + 1) curTag curLen rowEnds items
  else items
termination_by total.toNat - k.toNat

/-- The number of decimal digits of `n`. -/
def decimalLength (n : UInt32) : UInt32 :=
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

/-- The text of a run item; a count of 1 is left out. -/
def formatRLEItem (tag : UInt8) (count : UInt32) : String :=
  let tagStr := if tag == rleAlive then "o" else if tag == rleDead then "b" else if tag == rleRowEnd then "$" else "!"
  if count == 1 then tagStr else s!"{count}{tagStr}"

/-- The length of `formatRLEItem tag count`. -/
def formatRLEItemLength (count : UInt32) : UInt32 :=
  if count == 1 then 1 else decimalLength count + 1

/-- Lays out items `j` onward in lines of at most 70 characters, without splitting items. -/
def wrapRLEItems (items : Array (UInt8 × UInt32)) (numItems : UInt32) (j : UInt32) (line : String)
    (lineLen : UInt32) (out : GrowBuf String) : GrowBuf String :=
  if h : j < numItems then
    have : numItems.toNat - (j + 1).toNat < numItems.toNat - j.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (j + 1).toNat = j.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt numItems
        simp only [UInt32.toNat_one]
        omega
      omega
    let item := items[j.toNat]!
    let text := formatRLEItem item.1 item.2
    let len := formatRLEItemLength item.2
    if lineLen + len > 70 then
      wrapRLEItems items numItems (j + 1) text len (out.push line)
    else
      wrapRLEItems items numItems (j + 1) (line ++ text) (lineLen + len) out
  else if lineLen != 0 then out.push line else out
termination_by numItems.toNat - j.toNat

/-- The header lines for the box at (`minX`, `minY`) of size `width` by `height`. -/
def formatRLEHeader (minX minY : Int32) (width height : UInt32) : Array String :=
  #[s!"#R {minX} {minY}", s!"x = {width}, y = {height}, rule = B3/S23"]

/--
Serializes the cells in the bounding box from (`minX`, `minY`) to (`maxX`, `maxY`). Cells outside the box are
skipped.
-/
@[export rle_serialize]
def serializeRLE (cells : Array UInt64) (minX maxX minY maxY : Int32) : Array String :=
  if cells.size.toUInt32 == 0 then
    #["#R 0 0", "x = 0, y = 0, rule = B3/S23", "!"]
  else
    let width : UInt32 := (maxX - minX + 1).toUInt32
    let height : UInt32 := (maxY - minY + 1).toUInt32
    let grid := fillGrid cells minX minY width height rleAlive (by decide) 0 cells.size.toUInt32
      (AsciiBytes.replicate (width * height) rleDead (by decide))
    let items := (gridItems grid width (width * height) 0 rleDead 0 0 GrowBuf.empty).toArray
    let items := items.push (rleEnd, 1)
    let header := formatRLEHeader minX minY width height
    (wrapRLEItems items items.size.toUInt32 0 "" 0 (GrowBuf.empty.push header[0]! |>.push header[1]!)).toArray

end Algorithm

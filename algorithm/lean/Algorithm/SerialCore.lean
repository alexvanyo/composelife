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

/-!
# Shared helpers for the pattern file formats

The Kotlin backend lowers `Array.push` to a full copy, so building an array by repeated pushes costs O(n²).
`GrowBuf` keeps spare capacity so a push is amortized O(1); `set!` on a uniquely owned array is in place.

The parsers read lines as UTF-8 bytes. `parseInt32At` and `parseUInt32At` fail on values that don't fit
instead of wrapping around.
-/

/-- Whether `b` is an ASCII decimal digit. -/
@[inline]
def isDigitByte (b : UInt8) : Bool := b >= 48 && b <= 57

/-- Whether `b` is an ASCII space, tab or carriage return. -/
@[inline]
def isSpaceByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 13

/-- Whether `b` starts a UTF-8 encoded character (it is not a continuation byte). -/
@[inline]
def isCharStartByte (b : UInt8) : Bool := b &&& 0xC0 != 0x80

/--
An array with spare capacity. The live elements are the first `size` elements of `data`; the rest are
unused filler.
-/
structure GrowBuf (α : Type) where
  data : Array α
  size : UInt32

/-- An empty buffer. Each use is a separate allocation, so two buffers never share storage. -/
@[never_extract, noinline]
def GrowBuf.empty : GrowBuf α := ⟨Array.emptyWithCapacity 16, 0⟩

/-- Copies `src[i]` for `i` from `i` until `n` into `dst`. -/
def copyPrefix [Inhabited α] (src : Array α) (n : UInt32) (i : UInt32) (dst : Array α) : Array α :=
  if h : i < n then
    have : n.toNat - (i + 1).toNat < n.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt n
        simp only [UInt32.toNat_one]
        omega
      omega
    copyPrefix src n (i + 1) (dst.set! i.toNat src[i.toNat]!)
  else dst
termination_by n.toNat - i.toNat

/-- Appends `x`, doubling the capacity when the buffer is full. -/
def GrowBuf.push (b : GrowBuf α) (x : α) : GrowBuf α :=
  if b.size < b.data.size.toUInt32 then
    ⟨b.data.set! b.size.toNat x, b.size + 1⟩
  else
    let cap := b.data.size.toUInt32
    have : Inhabited α := ⟨x⟩
    let grown := copyPrefix b.data cap 0 (Array.replicate (2 * cap + 1).toNat x)
    ⟨grown, b.size + 1⟩

/-- The live elements of the buffer. -/
def GrowBuf.toArray (b : GrowBuf α) : Array α :=
  b.data.extract 0 b.size.toNat

/--
Scans decimal digits starting at `p`, returning the position after the last digit and the value accumulated
onto `acc`. Once the value exceeds 2^32 it stops growing, so it never wraps around.
-/
def scanDigits (bytes : ByteArray) (limit : UInt32) (p : UInt32) (acc : UInt64) : UInt32 × UInt64 :=
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
      scanDigits bytes limit (p + 1) (if acc > 4294967296 then acc else acc * 10 + (b.toUInt64 - 48))
    else (p, acc)
  else (p, acc)
termination_by limit.toNat - p.toNat

/-- A parsed `Int32` and the position after it. -/
structure ParsedInt32 where
  val : Int32
  next : UInt32
  deriving DecidableEq, Repr

/-- A parsed pair of coordinates. -/
structure ParsedCoords where
  x : Int32
  y : Int32
  deriving DecidableEq, Repr

/-- A parsed `UInt32` and the position after it. -/
structure ParsedUInt32 where
  val : UInt32
  next : UInt32
  deriving DecidableEq, Repr

/-- `x` as an `Int32`. Not inlined: the Kotlin backend would otherwise store an unconverted `UInt` in a field
read as `Int`. -/
@[noinline]
def uint32ToInt32 (x : UInt32) : Int32 := x.toInt32

/--
Parses an optionally negative decimal `Int32` starting at `pos`, returning the value and the position after
it. Fails if there are no digits or the value is out of range.
-/
def parseInt32At (bytes : ByteArray) (pos limit : UInt32) : Option ParsedInt32 :=
  let isNeg := pos < limit && bytes.get! pos.toNat == 45
  let start := if isNeg then pos + 1 else pos
  let r := scanDigits bytes limit start 0
  let e := r.1
  let v := r.2
  if e == start then none
  else if isNeg then
    if v ≤ 2147483648 then some ⟨(0 : Int32) - v.toUInt32.toInt32, e⟩ else none
  else if v ≤ 2147483647 then some ⟨uint32ToInt32 v.toUInt32, e⟩ else none

/--
Parses a decimal `UInt32` starting at `pos`, returning the value and the position after it. Fails if there
are no digits or the value is out of range.
-/
def parseUInt32At (bytes : ByteArray) (pos limit : UInt32) : Option ParsedUInt32 :=
  let r := scanDigits bytes limit pos 0
  if r.1 == pos then none
  else if r.2 ≤ 4294967295 then some ⟨r.2.toUInt32, r.1⟩ else none

/-- Skips spaces, tabs and carriage returns starting at `pos`. -/
def skipSpaces (bytes : ByteArray) (pos limit : UInt32) : UInt32 :=
  if h : pos < limit then
    have : limit.toNat - (pos + 1).toNat < limit.toNat - pos.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (pos + 1).toNat = pos.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    if isSpaceByte (bytes.get! pos.toNat) then
      skipSpaces bytes (pos + 1) limit
    else
      pos
  else
    pos
termination_by limit.toNat - pos.toNat

/--
Decodes the character starting at byte `p < limit` of UTF-8 `bytes`, returning its code point and the position
of the next character. Malformed input decodes one byte at a time.
-/
def decodeCharAt (bytes : ByteArray) (p limit : UInt32) : UInt32 × UInt32 :=
  let b0 := (bytes.get! p.toNat).toUInt32
  let cont (k : UInt32) : UInt32 := (bytes.get! (p + k).toNat).toUInt32 &&& 0x3F
  if b0 < 0x80 then (b0, p + 1)
  else if b0 &&& 0xE0 == 0xC0 && limit - p > 1 then
    (((b0 &&& 0x1F) <<< 6) ||| cont 1, p + 2)
  else if b0 &&& 0xF0 == 0xE0 && limit - p > 2 then
    (((b0 &&& 0x0F) <<< 12) ||| (cont 1 <<< 6) ||| cont 2, p + 3)
  else if b0 &&& 0xF8 == 0xF0 && limit - p > 3 then
    (((b0 &&& 0x07) <<< 18) ||| (cont 1 <<< 12) ||| (cont 2 <<< 6) ||| cont 3, p + 4)
  else (b0, p + 1)

theorem decodeCharAt_next (bytes : ByteArray) (p limit : UInt32) (h : p < limit) :
    p.toNat < (decodeCharAt bytes p limit).2.toNat ∧ (decodeCharAt bytes p limit).2.toNat ≤ limit.toNat := by
  have hp := UInt32.lt_iff_toNat_lt.mp h
  have hl := UInt32.toNat_lt limit
  have hsub : (limit - p).toNat = limit.toNat - p.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt h)
  have hadd : ∀ k : UInt32, k.toNat ≤ limit.toNat - p.toNat → (p + k).toNat = p.toNat + k.toNat := by
    intro k hk
    rw [UInt32.toNat_add]; omega
  unfold decodeCharAt
  simp only
  split
  · rw [hadd 1 (by simp; omega)]; simp; omega
  · split
    · rename_i h2
      have : (limit - p).toNat > 1 := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        exact UInt32.lt_iff_toNat_lt.mp h2.2
      rw [hadd 2 (by simp; omega)]; simp; omega
    · split
      · rename_i _ h3
        have : (limit - p).toNat > 2 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
          exact UInt32.lt_iff_toNat_lt.mp h3.2
        rw [hadd 3 (by simp; omega)]; simp; omega
      · split
        · rename_i _ _ h4
          have : (limit - p).toNat > 3 := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
            exact UInt32.lt_iff_toNat_lt.mp h4.2
          rw [hadd 4 (by simp; omega)]; simp; omega
        · rw [hadd 1 (by simp; omega)]; simp; omega

/-- An ASCII byte decodes to itself. -/
theorem decodeCharAt_ascii (bytes : ByteArray) (p limit : UInt32) (h : (bytes.get! p.toNat) < 128) :
    decodeCharAt bytes p limit = ((bytes.get! p.toNat).toUInt32, p + 1) := by
  unfold decodeCharAt
  have : (bytes.get! p.toNat).toUInt32 < 0x80 := by
    rw [UInt32.lt_iff_toNat_lt]; simp; exact h
  simp [this]

/--
Scans decimal digits starting at `p`, returning the position after the last digit and the set of digits seen
as a bit mask (bit `d` for digit `d`).
-/
def scanDigitSet (bytes : ByteArray) (limit : UInt32) (p : UInt32) (mask : UInt32) : UInt32 × UInt32 :=
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
      scanDigitSet bytes limit (p + 1) (mask ||| ((1 : UInt32) <<< (b.toUInt32 - 48)))
    else (p, mask)
  else (p, mask)
termination_by limit.toNat - p.toNat

/-- The digit set {2, 3}, the survival digits of Conway's rules. -/
def survival23Mask : UInt32 := 12

/-- The digit set {3}, the birth digits of Conway's rules. -/
def birth3Mask : UInt32 := 8

/-- Whether every byte of `b` is ASCII. -/
def AllAscii (b : ByteArray) : Prop := ∀ (i : Nat) (h : i < b.size), b[i] < 128

/-- The character with code point `x`. -/
def byteChar (x : UInt8) : Char :=
  ⟨x.toUInt32, Or.inl (by have := x.toNat_lt; simp [UInt8.toNat_toUInt32]; omega)⟩

theorem utf8EncodeChar_byteChar (x : UInt8) (hx : x < 128) :
    String.utf8EncodeChar (byteChar x) = [x] := by
  have hx' : x.toNat < 128 := hx
  have hv : (byteChar x).val.toNat = x.toNat := by simp [byteChar]
  simp only [String.utf8EncodeChar, hv, show x.toNat ≤ 0x7f by omega, ite_true]
  simp

theorem flatMap_utf8EncodeChar_ascii (l : List UInt8) (h : ∀ x ∈ l, x < 128) :
    (l.map byteChar).flatMap String.utf8EncodeChar = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.flatMap_cons, utf8EncodeChar_byteChar x (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem isValidUTF8_of_allAscii {b : ByteArray} (h : AllAscii b) : b.IsValidUTF8 := by
  refine ⟨b.data.toList.map byteChar, ?_⟩
  have hl : ∀ x ∈ b.data.toList, x < 128 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < b.size := by rw [ByteArray.size]; exact Array.length_toList ▸ hi
    have := h i hi'
    simpa [ByteArray.getElem_eq_getElem_data, Array.getElem_toList] using this
  rw [List.utf8Encode, flatMap_utf8EncodeChar_ascii _ hl]

/-- The string whose UTF-8 encoding is the ASCII bytes `b`. -/
@[inline]
def asciiString (b : ByteArray) (h : AllAscii b) : String :=
  String.ofByteArray b (isValidUTF8_of_allAscii h)

/-! ## ASCII grids -/

/-- A byte array holding only ASCII bytes. -/
abbrev AsciiBytes := {b : ByteArray // AllAscii b}

/-- `n` copies of the ASCII byte `v`. -/
def AsciiBytes.replicate (n : UInt32) (v : UInt8) (hv : v < 128) : AsciiBytes :=
  ⟨⟨Array.replicate n.toNat v⟩, by
    intro i hi
    show (Array.replicate n.toNat v)[i]'hi < 128
    rw [Array.getElem_replicate]
    exact hv⟩

/-- Sets byte `i` to the ASCII byte `v`, if it is in bounds. -/
def AsciiBytes.set (g : AsciiBytes) (i : UInt32) (v : UInt8) (hv : v < 128) : AsciiBytes :=
  ⟨g.1.set! i.toNat v, by
    intro j hj
    rw [ByteArray.size_set!] at hj
    by_cases hij : i.toNat = j
    · subst hij; rw [ByteArray.getElem_set!_self _ _ _ hj]; exact hv
    · rw [ByteArray.getElem_set!_ne _ _ _ _ hij]; exact g.2 j hj⟩

/-- The string of bytes `s` until `e`. -/
def AsciiBytes.toStringRange (g : AsciiBytes) (s e : UInt32) : String :=
  asciiString (g.1.extract s.toNat e.toNat) (by
    intro i hi
    rw [ByteArray.getElem_extract]
    exact g.2 _ _)

/--
The bits of a cell's coordinates. Serializers take cells this way: the Kotlin backend reads `Int32`s from a
generic array inconsistently, as `Int` or `UInt`, while `UInt32`s are always `UInt`.
-/
def cellBits (c : Int32 × Int32) : UInt32 × UInt32 := (c.1.toUInt32, c.2.toUInt32)

/--
Sets the grid byte of every cell (as `cellBits`) inside the `width` by `height` box at (`minX`, `minY`) to
`alive`. The grid is row major. Cells outside the box are skipped.
-/
def fillGrid (cells : Array (UInt32 × UInt32)) (minX minY : Int32) (width height : UInt32) (alive : UInt8)
    (halive : alive < 128) (i : UInt32) (limit : UInt32) (g : AsciiBytes) : AsciiBytes :=
  if h : i < limit then
    have : limit.toNat - (i + 1).toNat < limit.toNat - i.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt limit
        simp only [UInt32.toNat_one]
        omega
      omega
    let c := cells[i.toNat]!
    let dx := (c.1.toInt32 - minX).toUInt32
    let dy := (c.2.toInt32 - minY).toUInt32
    let g := if dx < width && dy < height then g.set (dy * width + dx) alive halive else g
    fillGrid cells minX minY width height alive halive (i + 1) limit g
  else g
termination_by limit.toNat - i.toNat

/-- Appends rows `r` onward of a row-major grid as strings. -/
def gridRows (g : AsciiBytes) (width height : UInt32) (r : UInt32) (acc : GrowBuf String) : GrowBuf String :=
  if h : r < height then
    have : height.toNat - (r + 1).toNat < height.toNat - r.toNat := by
      have h1 := UInt32.lt_iff_toNat_lt.mp h
      have h2 : (r + 1).toNat = r.toNat + 1 := by
        rw [UInt32.toNat_add]
        have := UInt32.toNat_lt height
        simp only [UInt32.toNat_one]
        omega
      omega
    gridRows g width height (r + 1) (acc.push (g.toStringRange (r * width) (r * width + width)))
  else acc
termination_by height.toNat - r.toNat

end Algorithm

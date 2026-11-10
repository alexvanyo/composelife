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

import Algorithm.Plaintext
import proofs.SerialCoreProofs

namespace Algorithm

/-! ## Character counting -/

theorem countChars_ascii (b : ByteArray) (hb : b.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32) (acc : UInt32), b.size - p.toNat = n → p.toNat ≤ b.size →
      (∀ q, p.toNat ≤ q → ∀ (hq : q < b.size), b[q] < 128) →
      countChars b b.size.toUInt32 p acc = acc + (b.size - p.toNat).toUInt32 := by
  intro n
  induction n with
  | zero =>
    intro p acc hn hp _
    have hnot : ¬ p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [countChars]
    simp [hnot, hn]
  | succ n ih =>
    intro p acc hn hp hascii
    have hlt : p.toNat < b.size := by omega
    have hyes : p < b.size.toUInt32 := by rw [u32_lt_size_iff hb]; exact hlt
    have hsucc := u32_toNat_succ hlt hb
    rw [countChars]
    simp only [hyes, ↓reduceDIte]
    rw [decodeCharAt_ascii b p _ (by rw [byteArray_get!_eq hlt]; exact hascii _ (Nat.le_refl _) hlt)]
    simp only
    rw [ih (p + 1) (acc + 1) (by omega) (by omega) (fun q hq => hascii q (by omega)), hsucc]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_one, u32_size_toNat (show b.size - (p.toNat + 1) < 2 ^ 32 by omega),
      u32_size_toNat (show b.size - p.toNat < 2 ^ 32 by omega)]
    omega

/-! ## Pattern rows -/

/-- Every byte is `.` or `O`. -/
def IsRowBytes (B : ByteArray) : Prop := ∀ (q : Nat) (hq : q < B.size), B[q] = 46 ∨ B[q] = 79

/-- The alive cells of row `row` with bytes `B`, from byte `p` on. -/
def rowCells (B : ByteArray) (p : Nat) (row : UInt32) : List (Int32 × Int32) :=
  (List.range' p (B.size - p)).filterMap
    (fun c => if B[c]! = 79 then some (c.toUInt32.toInt32, row.toInt32) else none)

theorem rowCells_of_ge (B : ByteArray) (p : Nat) (row : UInt32) (h : B.size ≤ p) : rowCells B p row = [] := by
  simp [rowCells, show B.size - p = 0 by omega]

theorem rowCells_of_lt (B : ByteArray) (p : Nat) (row : UInt32) (h : p < B.size) :
    rowCells B p row =
      (if B[p]! = 79 then [(p.toUInt32.toInt32, row.toInt32)] else []) ++ rowCells B (p + 1) row := by
  unfold rowCells
  rw [show B.size - p = (B.size - (p + 1)) + 1 by omega, List.range'_succ, List.filterMap_cons]
  split <;> simp_all

theorem loop_row (lines : Array String) (numLines i : UInt32) (B : ByteArray) (hB : IsRowBytes B)
    (hb : B.size < 2 ^ 31) (hi : i < numLines) (rowIdx li ll : UInt32) (hl : Bool)
    (warns : GrowBuf PlaintextWarning) :
    ∀ (n : Nat) (p : UInt32) (cells : U64Buf) (a : Array (Int32 × Int32)),
      B.size - p.toNat = n → p.toNat ≤ B.size → U64Buf.Rep cells (a.map cellBits) →
      a.size + (B.size - p.toNat) < 2 ^ 31 →
      ∃ cells' : U64Buf, U64Buf.Rep cells' ((a ++ (rowCells B p.toNat rowIdx).toArray).map cellBits) ∧
        deserializePlaintext.loop lines numLines i true B B.size.toUInt32 p p rowIdx li ll hl warns cells =
        deserializePlaintext.loop lines numLines (i + 1) false B B.size.toUInt32 0 0 (rowIdx + 1) li ll hl warns
          cells' := by
  have hb32 : B.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro p cells a hn hp hrep ha
    have hnot : ¬ p < B.size.toUInt32 := by rw [u32_lt_size_iff hb32]; omega
    refine ⟨cells, by rw [rowCells_of_ge B p.toNat rowIdx (by omega)]; simpa using hrep, ?_⟩
    rw [deserializePlaintext.loop]
    simp only [hi, ↓reduceDIte, ite_true, hnot]
  | succ n ih =>
    intro p cells a hn hp hrep ha
    have hlt : p.toNat < B.size := by omega
    have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hb32]; exact hlt
    have hsucc := u32_toNat_succ hlt hb32
    have hbyte := hB p.toNat hlt
    have hascii : B.get! p.toNat < 128 := by
      rw [byteArray_get!_eq hlt]; rcases hbyte with h | h <;> rw [h] <;> decide
    rw [deserializePlaintext.loop]
    simp only [hi, ↓reduceDIte, ite_true, hyes]
    rw [decodeCharAt_ascii B p _ hascii]
    simp only
    rw [byteArray_get!_eq hlt, rowCells_of_lt B p.toNat rowIdx hlt, getElem!_pos B p.toNat hlt]
    rcases hbyte with h46 | h79
    · rw [h46]
      simp only [show ((46 : UInt8).toUInt32 == 46) = true by decide, ite_true,
        show ¬ ((46 : UInt8) = 79) by decide, ite_false, List.nil_append]
      obtain ⟨c', hc', heq⟩ := ih (p + 1) cells a (by omega) (by omega) hrep (by omega)
      rw [hsucc] at hc'
      exact ⟨c', hc', heq⟩
    · rw [h79]
      simp only [show ((79 : UInt8).toUInt32 == 46) = false by decide, Bool.false_eq_true, ite_false,
        show ((79 : UInt8).toUInt32 == 79) = true by decide, ite_true]
      have hpush := U64Buf.rep_push hrep (cellBits (p.toInt32, rowIdx.toInt32)) (by simp only [Array.size_map]; omega)
      rw [← Array.map_push] at hpush
      obtain ⟨c', hc', heq⟩ := ih (p + 1) _ _ (by omega) (by omega) hpush (by simp only [Array.size_push]; omega)
      rw [hsucc] at hc'
      refine ⟨c', ?_, heq⟩
      have hp' : p.toNat.toUInt32 = p := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega)]
      simpa [hp'] using hc'

/-! ## Pattern files -/

/-- Every line is a pattern row of `w ≥ 1` `.` and `O` characters. -/
def IsRowLines (lines : Array String) (w : Nat) : Prop :=
  1 ≤ w ∧ ∀ (r : Nat) (hr : r < lines.size), IsRowBytes lines[r].toByteArray ∧ lines[r].toByteArray.size = w

/-- The alive cells of lines `i` onward, read as pattern rows. -/
def linesCells (lines : Array String) (i : Nat) : List (Int32 × Int32) :=
  (List.range' i (lines.size - i)).flatMap (fun r => rowCells lines[r]!.toByteArray 0 r.toUInt32)

theorem linesCells_of_ge (lines : Array String) (i : Nat) (h : lines.size ≤ i) : linesCells lines i = [] := by
  simp [linesCells, show lines.size - i = 0 by omega]

theorem linesCells_of_lt (lines : Array String) (i : Nat) (h : i < lines.size) :
    linesCells lines i = rowCells lines[i]!.toByteArray 0 i.toUInt32 ++ linesCells lines (i + 1) := by
  unfold linesCells
  rw [show lines.size - i = (lines.size - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

theorem rowCells_length_le (B : ByteArray) (p : Nat) (row : UInt32) : (rowCells B p row).length ≤ B.size - p := by
  unfold rowCells
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem linesCells_length_le (lines : Array String) (w : Nat) (hl : IsRowLines lines w) :
    ∀ i, (linesCells lines i).length ≤ (lines.size - i) * w := by
  intro i
  induction h : lines.size - i generalizing i with
  | zero => rw [linesCells_of_ge lines i (by omega)]; simp
  | succ n ih =>
    rw [linesCells_of_lt lines i (by omega), List.length_append]
    have h1 := rowCells_length_le lines[i]!.toByteArray 0 i.toUInt32
    rw [getElem!_pos lines i (by omega), (hl.2 i (by omega)).2] at h1
    have h2 := ih (i + 1) (by omega)
    rw [getElem!_pos lines i (by omega)]
    rw [Nat.add_mul] at *
    simp only [Nat.one_mul] at *
    omega

theorem loop_rows (lines : Array String) (w : Nat) (hl : IsRowLines lines w) (hls : lines.size * w < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (B : ByteArray) (L : UInt32) (li : UInt32) (warns : GrowBuf PlaintextWarning)
      (wa : Array PlaintextWarning) (cells : U64Buf) (a : Array (Int32 × Int32)),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → warns.Rep wa → U64Buf.Rep cells (a.map cellBits) →
      a.size + (lines.size - i.toNat) * w < 2 ^ 31 →
      deserializePlaintext.loop lines lines.size.toUInt32 i false B L 0 0 i li w.toUInt32 true warns cells =
        ⟨wa, (a ++ (linesCells lines i.toNat).toArray).map cellBits⟩ := by
  have hw := hl.1
  have hsz32 : lines.size < 2 ^ 32 := by
    have : lines.size ≤ lines.size * w := Nat.le_mul_of_pos_right _ (by omega)
    omega
  intro n
  induction n with
  | zero =>
    intro i B L li warns wa cells a hn hi hw' hc ha
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hsz32]; omega
    rw [deserializePlaintext.loop]
    simp only [hnot, ↓reduceDIte, hw'.2.2.2, hc.2.2.2, linesCells_of_ge lines i.toNat (by omega)]
    simp
  | succ n ih =>
    intro i B L li warns wa cells a hn hi hw' hc ha
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hsz32]; exact hlt
    have hsucc := u32_toNat_succ hlt hsz32
    have hw31 : w < 2 ^ 31 := by
      have : w ≤ lines.size * w := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hw32 : w < 2 ^ 32 := by omega
    have hnlt : ¬ w.toUInt32 < w.toUInt32 := UInt32.lt_irrefl _
    obtain ⟨hrow, hsize⟩ := hl.2 i.toNat hlt
    generalize hB : lines[i.toNat].toByteArray = B' at hrow hsize
    have hB' : lines[i.toNat]!.toByteArray = B' := by rw [getElem!_pos lines i.toNat hlt]; exact hB
    have hlim : B'.size.toUInt32 = w.toUInt32 := by rw [hsize]
    have hne0 : ¬ (B'.size.toUInt32 == 0) = true := by
      rw [hlim]; intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h)
      rw [u32_size_toNat hw32] at this; simp at this; omega
    have h0 : 0 < B'.size := by omega
    have hfirst : ¬ (B'.get! 0 == 33) = true := by
      rw [byteArray_get!_eq h0]
      rcases hrow 0 h0 with h | h <;> rw [h] <;> decide
    have hcount : countChars B' B'.size.toUInt32 0 0 = w.toUInt32 := by
      rw [countChars_ascii B' (by omega) _ 0 0 rfl (by simp) (by
        intro q _ hq; rcases hrow q hq with h | h <;> rw [h] <;> decide)]
      simp [hsize]
    rw [deserializePlaintext.loop]
    simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hB', hne0, hfirst, hcount, Bool.not_true,
      gt_iff_lt, hnlt]
    have hr := loop_row lines lines.size.toUInt32 i B' hrow (by omega) hyes i li w.toUInt32 true warns _ 0 cells a
      rfl (by simp) hc (by
        have : 1 * w ≤ (lines.size - i.toNat) * w := Nat.mul_le_mul_right _ (by omega)
        omega)
    obtain ⟨c', hc', heq⟩ := hr
    simp only [UInt32.toNat_zero] at hc'
    rw [heq, ih (i + 1) B' B'.size.toUInt32 li warns wa c' _ (by omega) (by omega) hw' hc' (by
      have h1 := rowCells_length_le B' 0 i
      simp only [Array.size_append, List.size_toArray, hsucc]
      rw [show lines.size - i.toNat = (lines.size - (i.toNat + 1)) + 1 by omega, Nat.add_mul] at ha
      omega)]
    rw [linesCells_of_lt lines i.toNat hlt, hB', hsucc]
    have hi' : i.toNat.toUInt32 = i := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega)]
    simp [hi', Array.append_assoc]

/-- Deserializing pattern rows gives their alive cells, in row-major order, with no warnings. -/
theorem deserializePlaintext_rows (lines : Array String) (w : Nat) (hl : IsRowLines lines w)
    (hls : lines.size * w < 2 ^ 31) (hne : 1 ≤ lines.size) :
    deserializePlaintext lines = ⟨#[], (linesCells lines 0).toArray.map cellBits⟩ := by
  have hw := hl.1
  have hsz32 : lines.size < 2 ^ 32 := by
    have : lines.size ≤ lines.size * w := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hw31 : w < 2 ^ 31 := by
    have : w ≤ lines.size * w := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hw32 : w < 2 ^ 32 := by omega
  have hyes : (0 : UInt32) < lines.size.toUInt32 := by rw [u32_lt_size_iff hsz32]; simp; omega
  obtain ⟨hrow, hsize⟩ := hl.2 0 (by omega)
  generalize hB : lines[0].toByteArray = B' at hrow hsize
  have hB' : lines[(0 : UInt32).toNat]!.toByteArray = B' := by
    rw [UInt32.toNat_zero, getElem!_pos lines 0 (by omega)]; exact hB
  have hne0 : ¬ (B'.size.toUInt32 == 0) = true := by
    rw [hsize]; intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h)
    rw [u32_size_toNat hw32] at this; simp at this; omega
  have h0 : 0 < B'.size := by omega
  have hfirst : ¬ (B'.get! 0 == 33) = true := by
    rw [byteArray_get!_eq h0]
    rcases hrow 0 h0 with h | h <;> rw [h] <;> decide
  have hcount : countChars B' B'.size.toUInt32 0 0 = w.toUInt32 := by
    rw [countChars_ascii B' (by omega) _ 0 0 rfl (by simp) (by
      intro q _ hq; rcases hrow q hq with h | h <;> rw [h] <;> decide)]
    simp [hsize]
  unfold deserializePlaintext
  rw [deserializePlaintext.loop]
  simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hB', hne0, hfirst, hcount, Bool.not_false,
    ite_true]
  obtain ⟨c', hc', heq⟩ := loop_row lines lines.size.toUInt32 0 B' hrow (by omega) hyes 0 (0 + 1) w.toUInt32 true
    GrowBuf.empty _ 0 U64Buf.empty #[] rfl (by simp) (by simpa using U64Buf.rep_empty) (by simp; omega)
  simp only [UInt32.toNat_zero] at hc'
  rw [heq]
  rw [loop_rows lines w hl hls _ (0 + 1) B' B'.size.toUInt32 (0 + 1) GrowBuf.empty #[] c' _ rfl (by simp; omega)
    GrowBuf.rep_empty hc' (by
      have h1 := rowCells_length_le B' 0 0
      have h2 : (lines.size - 1 + 1) * w = lines.size * w := by rw [Nat.sub_add_cancel (by omega)]
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp
      omega)]
  rw [linesCells_of_lt lines 0 (by omega), getElem!_pos lines 0 (by omega), hB]
  simp

/-! ## Serialization -/

/-- The grid of the serialized cells. -/
def plaintextGrid (cells : Array UInt64) (minX maxX minY maxY : Int32) : AsciiBytes :=
  let w : UInt32 := (maxX - minX + 1).toUInt32
  let h : UInt32 := (maxY - minY + 1).toUInt32
  fillGrid cells minX minY w h 79 (by decide) 0 cells.size.toUInt32 (AsciiBytes.replicate (w * h) 46 (by decide))

theorem serializePlaintext_eq (cells : Array UInt64) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 32) (hh : (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    serializePlaintext cells minX maxX minY maxY =
      ((List.range (maxY - minY + 1).toUInt32.toNat).map (fun k =>
        (plaintextGrid cells minX maxX minY maxY).toStringRange (k.toUInt32 * (maxX - minX + 1).toUInt32)
          (k.toUInt32 * (maxX - minX + 1).toUInt32 + (maxX - minX + 1).toUInt32))).toArray := by
  unfold serializePlaintext
  have h0 : ¬ (cells.size.toUInt32 == 0) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h)
    rw [u32_size_toNat hcs, UInt32.toNat_zero] at this
    exact hne this
  simp only [h0, Bool.false_eq_true, ite_false]
  have := gridRows_spec (plaintextGrid cells minX maxX minY maxY) (maxX - minX + 1).toUInt32
    (maxY - minY + 1).toUInt32 hh _ 0 GrowBuf.empty #[] rfl (by simp) GrowBuf.rep_empty
    (by rw [UInt32.toNat_zero, Nat.sub_zero, Array.size_empty, Nat.zero_add]; exact hh)
  show (gridRows (plaintextGrid cells minX maxX minY maxY) _ _ 0 GrowBuf.empty).toArray = _
  rw [this.2.2.2, UInt32.toNat_zero, Nat.sub_zero, ← List.range_eq_range', Array.empty_append]

open Classical in
/-- What the serialized grid holds. -/
theorem plaintextGrid_spec (cells : Array UInt64) (minX maxX minY maxY : Int32)
    (hcs : cells.size < 2 ^ 32)
    (hwh : (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat < 2 ^ 32) :
    (plaintextGrid cells minX maxX minY maxY).1.size =
        (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat ∧
      ∀ (k : Nat), k < (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat →
        (plaintextGrid cells minX maxX minY maxY).1[k]! =
          if ∃ c ∈ cells, gridIndex minX minY (maxX - minX + 1).toUInt32 (maxY - minY + 1).toUInt32
            ((cellKeyX c).toInt32, (cellKeyY c).toInt32) = some k
          then 79 else 46 := by
  generalize hw : (maxX - minX + 1).toUInt32 = w at hwh ⊢
  generalize hh : (maxY - minY + 1).toUInt32 = h at hwh ⊢
  have hsz : (AsciiBytes.replicate (w * h) 46 (by decide)).1.size = w.toNat * h.toNat := by
    simp [AsciiBytes.replicate, ByteArray.size, UInt32.toNat_mul, Nat.mod_eq_of_lt hwh]
  have := fillGrid_spec cells minX minY w h 79 (by decide) hwh hcs _ 0 _ rfl (by simp) hsz
  unfold plaintextGrid
  rw [hw, hh]
  refine ⟨by rw [this.1, hsz], fun k hk => ?_⟩
  rw [this.2 k (by rw [hsz]; exact hk)]
  have hinit : (AsciiBytes.replicate (w * h) 46 (by decide)).1[k]'(by rw [hsz]; exact hk) = 46 := by
    simp [AsciiBytes.replicate, ByteArray.getElem_eq_getElem_data]
  rw [hinit]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, -, hj, hk⟩; exact ⟨cells[j], Array.getElem_mem hj, hk⟩
  · rintro ⟨c, hc, hk⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hc
    exact ⟨j, by simp, hj, hk⟩

theorem mem_rowCells (B : ByteArray) (row : UInt32) (q : Int32 × Int32) :
    q ∈ rowCells B 0 row ↔ ∃ c, c < B.size ∧ B[c]! = 79 ∧ q = (c.toUInt32.toInt32, row.toInt32) := by
  unfold rowCells
  simp only [List.mem_filterMap, List.mem_range'_1, Nat.zero_add, Nat.sub_zero]
  constructor
  · rintro ⟨c, ⟨-, hc⟩, hq⟩
    split at hq
    · rename_i h79; simp only [Option.some.injEq] at hq; exact ⟨c, hc, h79, hq.symm⟩
    · simp at hq
  · rintro ⟨c, hc, h79, rfl⟩
    exact ⟨c, ⟨Nat.zero_le _, hc⟩, by simp [h79]⟩

theorem mem_linesCells (lines : Array String) (q : Int32 × Int32) :
    q ∈ linesCells lines 0 ↔ ∃ r, r < lines.size ∧ q ∈ rowCells lines[r]!.toByteArray 0 r.toUInt32 := by
  unfold linesCells
  simp only [List.mem_flatMap, List.mem_range'_1, Nat.zero_add, Nat.sub_zero]
  constructor
  · rintro ⟨r, ⟨-, hr⟩, hq⟩; exact ⟨r, hr, hq⟩
  · rintro ⟨r, hr, hq⟩; exact ⟨r, ⟨Nat.zero_le _, hr⟩, hq⟩

/--
Round trip: deserializing serialized cells gives no warnings, and the alive cells are exactly the cells inside the
bounding box, moved so the box starts at the origin.
-/
theorem plaintext_round_trip (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hw : 1 ≤ (maxX - minX + 1).toUInt32.toNat) (hh : 1 ≤ (maxY - minY + 1).toUInt32.toNat)
    (hwh : (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).cells ↔
        ∃ c ∈ cells, (gridIndex minX minY (maxX - minX + 1).toUInt32 (maxY - minY + 1).toUInt32 c).isSome ∧
          q = (c.1 - minX, c.2 - minY) := by
  generalize hW : (maxX - minX + 1).toUInt32 = w at hw hwh
  generalize hH : (maxY - minY + 1).toUInt32 = h at hh hwh
  have hH31 : h.toNat < 2 ^ 31 := by
    have : h.toNat ≤ w.toNat * h.toNat := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hW31 : w.toNat < 2 ^ 31 := by
    have : w.toNat ≤ w.toNat * h.toNat := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hser := serializePlaintext_eq (cells.map cellBits) minX maxX minY maxY (by simpa using hne) (by simp; omega)
    (by rw [hH]; exact hH31)
  rw [hW, hH] at hser
  obtain ⟨hgsize, hgget⟩ := plaintextGrid_spec (cells.map cellBits) minX maxX minY maxY (by simp; omega)
    (by rw [hW, hH]; omega)
  rw [hW, hH] at hgsize hgget
  generalize hg : plaintextGrid (cells.map cellBits) minX maxX minY maxY = g at hser hgsize hgget
  generalize hL : serializePlaintext (cells.map cellBits) minX maxX minY maxY = L at hser
  -- Row `r` of the output holds bytes `r * w` until `(r + 1) * w` of the grid.
  have hLsize : L.size = h.toNat := by rw [hser]; simp
  have hidx : ∀ r, r < h.toNat → (r.toUInt32 * w).toNat = r * w.toNat ∧
      (r.toUInt32 * w + w).toNat = r * w.toNat + w.toNat := by
    intro r hr
    have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
    have h1 : (r.toUInt32 * w).toNat = r * w.toNat := by
      rw [UInt32.toNat_mul, u32_size_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨h1, ?_⟩
    rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  have hLrow : ∀ r (hr : r < L.size), L[r].toByteArray = g.1.extract (r * w.toNat) (r * w.toNat + w.toNat) := by
    intro r hr
    have hr' : r < h.toNat := by omega
    simp only [hser, List.getElem_toArray, List.getElem_map, List.getElem_range]
    show (g.1.extract _ _) = _
    rw [(hidx r hr').1, (hidx r hr').2]
  have hrowbyte : ∀ r (hr : r < L.size) c, c < w.toNat → L[r].toByteArray[c]! = g.1[r * w.toNat + c]! := by
    intro r hr c hc
    have hr' : r < h.toNat := by omega
    have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
    rw [hLrow r hr]
    have hcs' : c < (g.1.extract (r * w.toNat) (r * w.toNat + w.toNat)).size := by
      rw [ByteArray.size_extract, hgsize]; omega
    rw [getElem!_pos _ c hcs', ByteArray.getElem_extract, getElem!_pos g.1 _ (by rw [hgsize]; omega)]
  have hgval : ∀ k, k < w.toNat * h.toNat → g.1[k]! = 46 ∨ g.1[k]! = 79 := by
    intro k hk
    rw [hgget k hk]
    split <;> simp
  -- The output is pattern rows.
  have hrows : IsRowLines L w.toNat := by
    refine ⟨hw, fun r hr => ⟨fun c hc => ?_, ?_⟩⟩
    · have hsz : L[r].toByteArray.size = w.toNat := by
        have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
        rw [hLrow r hr, ByteArray.size_extract, hgsize]; omega
      have := hrowbyte r hr c (by omega)
      rw [getElem!_pos _ c hc] at this
      rw [this]
      have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
      exact hgval _ (by omega)
    · have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
      rw [hLrow r hr, ByteArray.size_extract, hgsize]; omega
  rw [deserializePlaintext_rows L w.toNat hrows (by rw [hLsize, Nat.mul_comm]; exact hwh) (by omega)]
  refine ⟨rfl, fun q => ?_⟩
  rw [List.map_toArray, List.mem_toArray, cellBits_mem_map]
  simp only [mem_linesCells, mem_rowCells]
  constructor
  · rintro ⟨r, hr, c, hc, h79, rfl⟩
    have hsz : L[r]!.toByteArray.size = w.toNat := by rw [getElem!_pos L r hr]; exact (hrows.2 r hr).2
    rw [hsz] at hc
    rw [getElem!_pos L r hr, hrowbyte r hr c hc] at h79
    have hk : r * w.toNat + c < w.toNat * h.toNat := by
      have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle; omega
    rw [hgget _ hk] at h79
    split at h79
    · rename_i hex
      obtain ⟨cb, hcb, hidx'⟩ := hex
      obtain ⟨cell, hcell, rfl⟩ := Array.mem_map.mp hcb
      simp only [keyX_cellBits, keyY_cellBits, Int32.toInt32_toUInt32] at hidx'
      obtain ⟨hx, hy, hrr, hcc⟩ := (gridIndex_eq_iff hc).mp hidx'
      refine ⟨cell, hcell, by rw [hidx']; rfl, ?_⟩
      have h1 : c.toUInt32 = (cell.1 - minX).toUInt32 := by
        apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega), hcc]
      have h2 : r.toUInt32 = (cell.2 - minY).toUInt32 := by
        apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega), hrr]
      rw [h1, h2]
      rfl
    · simp at h79
  · rintro ⟨cell, hcell, hsome, rfl⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
    unfold gridIndex at hk
    split at hk
    · rename_i hin
      simp only [Option.some.injEq] at hk
      have hx := UInt32.lt_iff_toNat_lt.mp hin.1
      have hy := UInt32.lt_iff_toNat_lt.mp hin.2
      refine ⟨(cell.2 - minY).toUInt32.toNat, by omega, (cell.1 - minX).toUInt32.toNat, ?_, ?_, ?_⟩
      · rw [getElem!_pos L _ (by omega), (hrows.2 _ (by omega)).2]; exact hx
      · rw [getElem!_pos L _ (by omega), hrowbyte _ (by omega) _ hx]
        have hk' : (cell.2 - minY).toUInt32.toNat * w.toNat + (cell.1 - minX).toUInt32.toNat < w.toNat * h.toNat :=
          gridIndex_lt (k := _) (by unfold gridIndex; rw [ite_eq_left hin])
        rw [hgget _ hk', ite_eq_left ⟨cellBits cell, Array.mem_map_of_mem hcell, by
          simp only [keyX_cellBits, keyY_cellBits, Int32.toInt32_toUInt32]; unfold gridIndex; rw [ite_eq_left hin]⟩]
      · simp
    · simp at hk

/--
Round trip for cells inside their bounding box: deserializing gives no warnings, and exactly the cells, moved so
the box starts at the origin.
-/
theorem plaintext_round_trip_box (cells : Array (Int32 × Int32)) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hbox : ∀ c ∈ cells, minX.toInt ≤ c.1.toInt ∧ c.1.toInt ≤ maxX.toInt ∧
      minY.toInt ≤ c.2.toInt ∧ c.2.toInt ≤ maxY.toInt)
    (hsize : (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) < 2 ^ 31) :
    (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializePlaintext (serializePlaintext (cells.map cellBits) minX maxX minY maxY)).cells ↔
        ∃ c ∈ cells, q = (c.1 - minX, c.2 - minY) := by
  obtain ⟨c0, hc0⟩ : ∃ c, c ∈ cells := ⟨cells[0]'(by omega), Array.getElem_mem _⟩
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hbox c0 hc0
  have hw1 : 1 ≤ maxX.toInt - minX.toInt + 1 := by omega
  have hh1 : 1 ≤ maxY.toInt - minY.toInt + 1 := by omega
  have hw : maxX.toInt - minX.toInt + 1 < 2 ^ 31 := by
    have : (maxX.toInt - minX.toInt + 1) * 1 ≤ (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) :=
      Int.mul_le_mul_of_nonneg_left hh1 (by omega)
    omega
  have hh : maxY.toInt - minY.toInt + 1 < 2 ^ 31 := by
    have : 1 * (maxY.toInt - minY.toInt + 1) ≤ (maxX.toInt - minX.toInt + 1) * (maxY.toInt - minY.toInt + 1) :=
      Int.mul_le_mul_of_nonneg_right hw1 (by omega)
    omega
  have hW := boxSize_toNat minX maxX (by omega) hw
  have hH := boxSize_toNat minY maxY (by omega) hh
  have hwh : (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31 := by
    have : (((maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat : Nat) : Int) < 2 ^ 31 := by
      rw [Int.natCast_mul, hW, hH]; exact hsize
    omega
  obtain ⟨hwarn, hcells⟩ := plaintext_round_trip cells minX maxX minY maxY hne hcs (by omega) (by omega) hwh
  refine ⟨hwarn, fun q => ?_⟩
  rw [hcells]
  constructor
  · rintro ⟨c, hc, -, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hbox c hc
    exact ⟨c, hc, gridIndex_isSome_of_mem_box minX maxX minY maxY c hx1 hx2 hy1 hy2 hw hh, rfl⟩

/--
Round trip of whole patterns: `serializePlaintextCells` writes the cells in their bounding box, and deserializing
gives no warnings and exactly the cells, moved so the least x and the least y are 0.
-/
theorem plaintext_round_trip_cells (cells : Array (Int32 × Int32)) (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hsize : ∀ c ∈ cells, ∀ d ∈ cells, ∀ e ∈ cells, ∀ f ∈ cells,
      (c.1.toInt - d.1.toInt + 1) * (e.2.toInt - f.2.toInt + 1) < 2 ^ 31) :
    let b := cellBox (cells.map cellBits)
    (∀ c ∈ cells, b.1.toInt ≤ c.1.toInt ∧ b.2.2.1.toInt ≤ c.2.toInt) ∧ (∃ c ∈ cells, c.1 = b.1) ∧
      (∃ c ∈ cells, c.2 = b.2.2.1) ∧
      (deserializePlaintext (serializePlaintextCells (cells.map cellBits))).warnings = #[] ∧
      ∀ q, cellBits q ∈ (deserializePlaintext (serializePlaintextCells (cells.map cellBits))).cells ↔
        ∃ c ∈ cells, q = (c.1 - b.1, c.2 - b.2.2.1) := by
  intro b
  obtain ⟨hall, ⟨c1, hc1, e1⟩, ⟨c2, hc2, e2⟩, ⟨c3, hc3, e3⟩, ⟨c4, hc4, e4⟩⟩ :=
    cellBox_map_facts cells (by omega) hne b rfl
  have hser : serializePlaintextCells (cells.map cellBits) =
      serializePlaintext (cells.map cellBits) b.1 b.2.1 b.2.2.1 b.2.2.2 := rfl
  rw [hser]
  have := hsize c2 hc2 c1 hc1 c4 hc4 c3 hc3
  rw [e1, e2, e3, e4] at this
  obtain ⟨hw, hm⟩ := plaintext_round_trip_box cells b.1 b.2.1 b.2.2.1 b.2.2.2 hne hcs hall this
  exact ⟨fun c hc => ⟨(hall c hc).1, (hall c hc).2.2.1⟩, ⟨c1, hc1, e1⟩, ⟨c3, hc3, e3⟩, hw, hm⟩

/--
Serialized cells are `h` pattern rows of `w` characters, each `.` or `O`, for the `w` by `h` bounding box.
-/
theorem serializePlaintext_rows (cells : Array UInt64) (minX maxX minY maxY : Int32)
    (hne : cells.size ≠ 0) (hcs : cells.size < 2 ^ 31)
    (hw : 1 ≤ (maxX - minX + 1).toUInt32.toNat) (hh : 1 ≤ (maxY - minY + 1).toUInt32.toNat)
    (hwh : (maxX - minX + 1).toUInt32.toNat * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    IsRowLines (serializePlaintext cells minX maxX minY maxY) (maxX - minX + 1).toUInt32.toNat ∧
      (serializePlaintext cells minX maxX minY maxY).size = (maxY - minY + 1).toUInt32.toNat := by
  generalize hW : (maxX - minX + 1).toUInt32 = w at hw hwh
  generalize hH : (maxY - minY + 1).toUInt32 = h at hh hwh
  have hH31 : h.toNat < 2 ^ 31 := by
    have : h.toNat ≤ w.toNat * h.toNat := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hW31 : w.toNat < 2 ^ 31 := by
    have : w.toNat ≤ w.toNat * h.toNat := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hser := serializePlaintext_eq cells minX maxX minY maxY hne (by omega)
    (by rw [hH]; exact hH31)
  rw [hW, hH] at hser
  obtain ⟨hgsize, hgget⟩ := plaintextGrid_spec cells minX maxX minY maxY (by omega)
    (by rw [hW, hH]; omega)
  rw [hW, hH] at hgsize hgget
  generalize hg : plaintextGrid cells minX maxX minY maxY = g at hser hgsize hgget
  generalize hL : serializePlaintext cells minX maxX minY maxY = L at hser
  -- Row `r` of the output holds bytes `r * w` until `(r + 1) * w` of the grid.
  have hLsize : L.size = h.toNat := by rw [hser]; simp
  have hidx : ∀ r, r < h.toNat → (r.toUInt32 * w).toNat = r * w.toNat ∧
      (r.toUInt32 * w + w).toNat = r * w.toNat + w.toNat := by
    intro r hr
    have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
    have h1 : (r.toUInt32 * w).toNat = r * w.toNat := by
      rw [UInt32.toNat_mul, u32_size_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨h1, ?_⟩
    rw [UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  have hLrow : ∀ r (hr : r < L.size), L[r].toByteArray = g.1.extract (r * w.toNat) (r * w.toNat + w.toNat) := by
    intro r hr
    have hr' : r < h.toNat := by omega
    simp only [hser, List.getElem_toArray, List.getElem_map, List.getElem_range]
    show (g.1.extract _ _) = _
    rw [(hidx r hr').1, (hidx r hr').2]
  have hrowbyte : ∀ r (hr : r < L.size) c, c < w.toNat → L[r].toByteArray[c]! = g.1[r * w.toNat + c]! := by
    intro r hr c hc
    have hr' : r < h.toNat := by omega
    have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
    rw [hLrow r hr]
    have hcs' : c < (g.1.extract (r * w.toNat) (r * w.toNat + w.toNat)).size := by
      rw [ByteArray.size_extract, hgsize]; omega
    rw [getElem!_pos _ c hcs', ByteArray.getElem_extract, getElem!_pos g.1 _ (by rw [hgsize]; omega)]
  have hgval : ∀ k, k < w.toNat * h.toNat → g.1[k]! = 46 ∨ g.1[k]! = 79 := by
    intro k hk
    rw [hgget k hk]
    split <;> simp
  -- The output is pattern rows.
  have hrows : IsRowLines L w.toNat := by
    refine ⟨hw, fun r hr => ⟨fun c hc => ?_, ?_⟩⟩
    · have hsz : L[r].toByteArray.size = w.toNat := by
        have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
        rw [hLrow r hr, ByteArray.size_extract, hgsize]; omega
      have := hrowbyte r hr c (by omega)
      rw [getElem!_pos _ c hc] at this
      rw [this]
      have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
      exact hgval _ (by omega)
    · have hle : (r + 1) * w.toNat ≤ h.toNat * w.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm h.toNat] at hle
      rw [hLrow r hr, ByteArray.size_extract, hgsize]; omega
  exact ⟨hrows, hLsize⟩

end Algorithm

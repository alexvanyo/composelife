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

import proofs.PlaintextProofs

namespace Algorithm

/-!
# Plaintext deserialization of any input

`deserializePlaintext` is `linesSpec` over the lines and their code points: comments are skipped, blank lines and
rows shorter than the longest row give warnings, and every character of a row other than `.` and `O` gives a
warning and is alive unless it is a space.
-/

/-- The code points of `bytes` from byte `p` until `limit`, as the deserializers decode them. -/
def codePointsFrom (bytes : ByteArray) (limit p : UInt32) : List UInt32 :=
  if _h : p < limit then
    (decodeCharAt bytes p limit).1 :: codePointsFrom bytes limit (decodeCharAt bytes p limit).2
  else []
termination_by limit.toNat - p.toNat
decreasing_by have := decodeCharAt_next bytes p limit _h; omega

/-- The code points of a line, as the deserializers decode them. -/
def codePoints (s : String) : List UInt32 := codePointsFrom s.toByteArray s.toByteArray.size.toUInt32 0

theorem codePointsFrom_length_le (bytes : ByteArray) (limit : UInt32) :
    ∀ (n : Nat) (p : UInt32), limit.toNat - p.toNat ≤ n →
      (codePointsFrom bytes limit p).length ≤ limit.toNat - p.toNat := by
  intro n
  induction n with
  | zero =>
    intro p hn
    rw [codePointsFrom]
    have : ¬ p < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    simp [this]
  | succ n ih =>
    intro p hn
    rw [codePointsFrom]
    by_cases h : p < limit
    · simp only [h, ↓reduceDIte, List.length_cons]
      have := decodeCharAt_next bytes p limit h
      have := ih (decodeCharAt bytes p limit).2 (by omega)
      omega
    · simp [h]

theorem countChars_eq (bytes : ByteArray) (limit : UInt32) :
    ∀ (n : Nat) (p acc : UInt32), limit.toNat - p.toNat ≤ n →
      countChars bytes limit p acc = acc + (codePointsFrom bytes limit p).length.toUInt32 := by
  intro n
  induction n with
  | zero =>
    intro p acc hn
    have : ¬ p < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [countChars, codePointsFrom]
    simp [this]
  | succ n ih =>
    intro p acc hn
    rw [countChars, codePointsFrom]
    by_cases h : p < limit
    · simp only [h, ↓reduceDIte, List.length_cons]
      have := decodeCharAt_next bytes p limit h
      rw [ih _ (acc + 1) (by omega)]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_one, Nat.toUInt32, UInt32.toNat_ofNat']
      omega
    · simp [h]

/--
The warnings and alive cells of a pattern row with code points `cps` from column `col` (0-based), on row `row` and
line `line` (1-based).
-/
def rowSpec (line row : UInt32) : UInt32 → List UInt32 → List PlaintextWarning × List (Int32 × Int32)
  | _, [] => ([], [])
  | col, cp :: cps =>
    let rest := rowSpec line row (col + 1) cps
    if cp = 46 then rest
    else if cp = 79 then (rest.1, (col.toInt32, row.toInt32) :: rest.2)
    else (.unexpectedChar line (col + 1) cp :: rest.1,
      if cp = 32 then rest.2 else (col.toInt32, row.toInt32) :: rest.2)

theorem rowSpec_length (line row : UInt32) :
    ∀ (cps : List UInt32) (col : UInt32), (rowSpec line row col cps).1.length ≤ cps.length ∧
      (rowSpec line row col cps).2.length ≤ cps.length := by
  intro cps
  induction cps with
  | nil => intro col; simp [rowSpec]
  | cons cp cps ih =>
    intro col
    obtain ⟨h1, h2⟩ := ih (col + 1)
    simp only [rowSpec]
    split
    · simp; omega
    · split
      · simp; omega
      · split <;> simp <;> omega

/--
The warnings and alive cells of lines `ls`, the first of which is line `i + 1` (1-based); `row` is the next pattern
row, and `longest` the line and length of the longest pattern row so far.
-/
def linesSpec : List String → UInt32 → UInt32 → Option (UInt32 × UInt32) →
    List PlaintextWarning × List (Int32 × Int32)
  | [], _, _, _ => ([], [])
  | l :: ls, i, row, longest =>
    if l.toByteArray.size = 0 then
      let rest := linesSpec ls (i + 1) row longest
      (if ls = [] then rest.1 else .blankLine (i + 1) :: rest.1, rest.2)
    else if l.toByteArray.get! 0 = 33 then linesSpec ls (i + 1) row longest
    else
      let cps := codePoints l
      let len := cps.length.toUInt32
      let lw : List PlaintextWarning × (UInt32 × UInt32) := match longest with
        | none => ([], (i + 1, len))
        | some (li, ll) =>
          if len > ll then ([.shortLine li], (i + 1, len))
          else (if len < ll then [.shortLine (i + 1)] else [], (li, ll))
      let r := rowSpec (i + 1) row 0 cps
      let rest := linesSpec ls (i + 1) (row + 1) (some lw.2)
      (lw.1 ++ r.1 ++ rest.1, r.2 ++ rest.2)

theorem loop_row_spec (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (bytes : ByteArray)
    (limit : UInt32) (row li ll : UInt32) (hl : Bool) :
    ∀ (n : Nat) (p col : UInt32) (warns : GrowBuf PlaintextWarning) (w : Array PlaintextWarning) (cells : U64Buf)
      (c : Array (Int32 × Int32)),
      limit.toNat - p.toNat ≤ n → warns.Rep w → U64Buf.Rep cells (c.map cellBits) →
      w.size + (limit.toNat - p.toNat) < 2 ^ 31 → c.size + (limit.toNat - p.toNat) < 2 ^ 31 →
      ∃ (warns' : GrowBuf PlaintextWarning) (cells' : U64Buf),
        warns'.Rep (w ++ (rowSpec (i + 1) row col (codePointsFrom bytes limit p)).1.toArray) ∧
        U64Buf.Rep cells' ((c ++ (rowSpec (i + 1) row col (codePointsFrom bytes limit p)).2.toArray).map cellBits) ∧
        deserializePlaintext.loop lines numLines i true bytes limit p col row li ll hl warns cells =
          deserializePlaintext.loop lines numLines (i + 1) false bytes limit 0 0 (row + 1) li ll hl warns' cells' := by
  intro n
  induction n with
  | zero =>
    intro p col warns w cells c hn hw hc _ _
    have hnot : ¬ p < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    refine ⟨warns, cells, ?_, ?_, ?_⟩
    · rw [codePointsFrom]; simpa [hnot, rowSpec] using hw
    · rw [codePointsFrom]; simpa [hnot, rowSpec] using hc
    · rw [deserializePlaintext.loop]; simp [hi, hnot]
  | succ n ih =>
    intro p col warns w cells c hn hw hc hws hcs
    by_cases hp : p < limit
    · have hnext := decodeCharAt_next bytes p limit hp
      have hcp : codePointsFrom bytes limit p =
          (decodeCharAt bytes p limit).1 :: codePointsFrom bytes limit (decodeCharAt bytes p limit).2 := by
        rw [codePointsFrom]; simp [hp]
      rw [hcp, deserializePlaintext.loop]
      simp only [hi, ↓reduceDIte, ite_true, hp]
      generalize hr : decodeCharAt bytes p limit = r at hnext ⊢
      obtain ⟨cp, p'⟩ := r
      simp only at hnext ⊢
      simp only [rowSpec]
      by_cases h46 : cp = 46
      · simp only [h46, beq_self_eq_true, ite_true]
        exact ih p' (col + 1) warns w cells c (by omega) hw hc (by omega) (by omega)
      · have h46' : (cp == 46) = false := by simpa using h46
        simp only [h46, h46', Bool.false_eq_true, ite_false]
        by_cases h79 : cp = 79
        · simp only [h79, beq_self_eq_true, ite_true]
          have hpush := U64Buf.rep_push hc (cellBits (col.toInt32, row.toInt32)) (by simp; omega)
          rw [← Array.map_push] at hpush
          obtain ⟨w', c', hw', hc', heq⟩ := ih p' (col + 1) warns w _ _ (by omega) hw hpush (by omega)
            (by simp; omega)
          refine ⟨w', c', hw', ?_, heq⟩
          simpa using hc'
        · have h79' : (cp == 79) = false := by simpa using h79
          simp only [h79, h79', Bool.false_eq_true, ite_false]
          have hwp := GrowBuf.rep_push hw (.unexpectedChar (i + 1) (col + 1) cp) (by omega)
          by_cases h32 : cp = 32
          · subst h32
            simp only [beq_self_eq_true, ite_true]
            obtain ⟨w', c', hw', hc', heq⟩ := ih p' (col + 1) _ _ cells c (by omega) hwp hc (by simp; omega)
              (by omega)
            exact ⟨w', c', by simpa using hw', hc', heq⟩
          · have h32' : (cp == 32) = false := by simpa using h32
            simp only [h32, h32', Bool.false_eq_true, ite_false]
            have hpush := U64Buf.rep_push hc (cellBits (col.toInt32, row.toInt32)) (by simp; omega)
            rw [← Array.map_push] at hpush
            obtain ⟨w', c', hw', hc', heq⟩ := ih p' (col + 1) _ _ _ _ (by omega) hwp hpush (by simp; omega)
              (by simp; omega)
            exact ⟨w', c', by simpa using hw', by simpa using hc', heq⟩
    · refine ⟨warns, cells, ?_, ?_, ?_⟩
      · rw [codePointsFrom]; simpa [hp, rowSpec] using hw
      · rw [codePointsFrom]; simpa [hp, rowSpec] using hc
      · rw [deserializePlaintext.loop]; simp [hi, hp]

theorem loop_lines_spec (lines : Array String) (hls : lines.size < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (B : ByteArray) (L row li ll : UInt32) (hl : Bool)
      (warns : GrowBuf PlaintextWarning) (w : Array PlaintextWarning) (cells : U64Buf) (c : Array (Int32 × Int32)),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → warns.Rep w → U64Buf.Rep cells (c.map cellBits) →
      w.size + remBytes (lines.toList.drop i.toNat) < 2 ^ 31 →
      c.size + remBytes (lines.toList.drop i.toNat) < 2 ^ 31 →
      deserializePlaintext.loop lines lines.size.toUInt32 i false B L 0 0 row li ll hl warns cells =
        ⟨w ++ (linesSpec (lines.toList.drop i.toNat) i row (if hl then some (li, ll) else none)).1.toArray,
          (c ++ (linesSpec (lines.toList.drop i.toNat) i row (if hl then some (li, ll) else none)).2.toArray).map
            cellBits⟩ := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i B L row li ll hl warns w cells c hn hi hw hc _ _
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; omega
    rw [deserializePlaintext.loop]
    simp [hnot, List.drop_eq_nil_of_le (show lines.toList.length ≤ i.toNat by simp; omega),
      linesSpec, hw.2.2.2, U64Buf.toArray_of_rep hc]
  | succ n ih =>
    intro i B L row li ll hl warns w cells c hn hi hw hc hws hcs
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; exact hlt
    have hsucc := u32_toNat_succ hlt hs32
    have hdrop := toList_drop_eq_cons lines i.toNat hlt
    rw [hdrop, remBytes_cons] at hws hcs
    rw [hdrop]
    have hl! : lines[i.toNat]! = lines[i.toNat] := getElem!_pos lines i.toNat hlt
    generalize hline : lines[i.toNat] = l at hl! hws hcs
    generalize hrest : lines.toList.drop (i.toNat + 1) = rest at hws hcs
    have hrest' : lines.toList.drop (i + 1).toNat = rest := by rw [hsucc, hrest]
    have hb32 : l.toByteArray.size < 2 ^ 32 := by omega
    rw [deserializePlaintext.loop]
    simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hl!]
    by_cases h0 : l.toByteArray.size = 0
    · simp only [h0, show ((0 : Nat).toUInt32 == 0) = true from rfl, ite_true, linesSpec]
      have hlast : (i + 1 < lines.size.toUInt32) ↔ rest ≠ [] := by
        rw [u32_lt_size_iff hs32, hsucc, ← hrest]
        simp
      by_cases hr : rest = []
      · have : ¬ (i + 1 < lines.size.toUInt32) := fun h => (hlast.mp h) hr
        simp only [this, ite_false, hr, ite_true]
        rw [ih (i + 1) _ _ row li ll hl warns w cells c (by omega) (by omega) hw hc
          (by rw [hrest', hr]; simp only [remBytes, List.map_nil, List.sum_nil]; omega)
          (by rw [hrest', hr]; simp only [remBytes, List.map_nil, List.sum_nil]; omega), hrest', hr]
      · have : i + 1 < lines.size.toUInt32 := hlast.mpr hr
        simp only [this, ite_true, hr, ite_false]
        rw [ih (i + 1) _ _ row li ll hl _ _ cells c (by omega) (by omega)
          (GrowBuf.rep_push hw (.blankLine (i + 1)) (by omega)) hc (by rw [hrest']; simp; omega)
          (by rw [hrest']; omega), hrest']
        simp
    · have hz : (l.toByteArray.size.toUInt32 == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro h
        have := congrArg UInt32.toNat h; rw [u32_size_toNat hb32, UInt32.toNat_zero] at this; omega
      simp only [hz, Bool.false_eq_true, ite_false, linesSpec, h0]
      by_cases h33 : l.toByteArray.get! 0 = 33
      · simp only [h33, beq_self_eq_true, ite_true]
        rw [ih (i + 1) _ _ row li ll hl warns w cells c (by omega) (by omega) hw hc (by rw [hrest']; omega)
          (by rw [hrest']; omega), hrest']
      · have h33' : (l.toByteArray.get! 0 == 33) = false := by simpa using h33
        simp only [h33, h33', Bool.false_eq_true, ite_false]
        have hcount : countChars l.toByteArray l.toByteArray.size.toUInt32 0 0 = (codePoints l).length.toUInt32 := by
          rw [countChars_eq _ _ _ 0 0 (Nat.le_refl _)]; simp [codePoints]
        rw [hcount]
        generalize hlen : (codePoints l).length.toUInt32 = len
        have hcpl := codePointsFrom_length_le l.toByteArray l.toByteArray.size.toUInt32 _ 0 (Nat.le_refl _)
        rw [u32_size_toNat hb32, UInt32.toNat_zero, Nat.sub_zero] at hcpl
        have hrow := rowSpec_length (i + 1) row (codePoints l) 0
        have hr1 : (rowSpec (i + 1) row 0 (codePoints l)).1.length ≤ l.toByteArray.size :=
          Nat.le_trans hrow.1 hcpl
        have hr2 : (rowSpec (i + 1) row 0 (codePoints l)).2.length ≤ l.toByteArray.size :=
          Nat.le_trans hrow.2 hcpl
        -- After the length check: the row, then the rest.
        have finish : ∀ (li' ll' : UInt32) (warns' : GrowBuf PlaintextWarning) (w' : Array PlaintextWarning),
            warns'.Rep w' → w'.size ≤ w.size + 1 →
            deserializePlaintext.loop lines lines.size.toUInt32 i true l.toByteArray l.toByteArray.size.toUInt32 0 0
                row li' ll' true warns' cells =
              ⟨w' ++ ((rowSpec (i + 1) row 0 (codePoints l)).1 ++
                  (linesSpec rest (i + 1) (row + 1) (some (li', ll'))).1).toArray,
                (c ++ ((rowSpec (i + 1) row 0 (codePoints l)).2 ++
                  (linesSpec rest (i + 1) (row + 1) (some (li', ll'))).2).toArray).map cellBits⟩ := by
          intro li' ll' warns' w' hw' hsz'
          obtain ⟨w2, c2, hw2, hc2, heq⟩ := loop_row_spec lines lines.size.toUInt32 i hyes l.toByteArray
            l.toByteArray.size.toUInt32 row li' ll' true _ 0 0 warns' w' cells c (Nat.le_refl _) hw' hc
            (by rw [u32_size_toNat hb32, UInt32.toNat_zero, Nat.sub_zero]; omega)
            (by rw [u32_size_toNat hb32, UInt32.toNat_zero, Nat.sub_zero]; omega)
          rw [heq, ih (i + 1) _ _ (row + 1) li' ll' true _ _ _ _ (by omega) (by omega) hw2 hc2
            (by rw [hrest']; simp only [Array.size_append, List.size_toArray]; simp only [codePoints] at hr1; omega)
            (by rw [hrest']; simp only [Array.size_append, List.size_toArray]; simp only [codePoints] at hr2; omega),
            hrest']
          simp [codePoints, Array.append_assoc]
        cases hl with
        | false =>
          simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
          rw [finish (i + 1) len warns w hw (by omega)]
          simp
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
          by_cases hgt : len > ll
          · simp only [hgt, ite_true]
            rw [finish (i + 1) len _ _ (GrowBuf.rep_push hw (.shortLine li) (by omega)) (by simp)]
            simp
          · simp only [hgt, ite_false]
            by_cases hlt' : len < ll
            · simp only [hlt', ite_true]
              rw [finish li ll _ _ (GrowBuf.rep_push hw (.shortLine (i + 1)) (by omega)) (by simp)]
              simp
            · simp only [hlt', ite_false]
              rw [finish li ll warns w hw (by omega)]
              simp

/-- Deserialization of any lines (of fewer than 2 ^ 31 bytes in all) is `linesSpec`. -/
theorem deserializePlaintext_eq_linesSpec_Impl (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 31) :
    deserializePlaintext lines =
      ⟨(linesSpec lines.toList 0 0 none).1.toArray, (linesSpec lines.toList 0 0 none).2.toArray.map cellBits⟩ := by
  unfold deserializePlaintext
  rw [loop_lines_spec lines hls _ 0 ByteArray.empty 0 0 0 0 false GrowBuf.empty #[] U64Buf.empty #[] rfl (by simp)
    GrowBuf.rep_empty (by simpa using U64Buf.rep_empty) (by simpa using hb) (by simpa using hb)]
  simp

/-! ## Concrete checks of the master theorems -/

/-- Proof of `deserializePlaintext_empty`. -/
theorem deserializePlaintext_empty_Impl : deserializePlaintext #[] = ⟨#[], #[]⟩ := by
  decide +kernel

/-- Proof of `deserializePlaintext_comments_ignored`. -/
theorem deserializePlaintext_comments_ignored_Impl :
    deserializePlaintext #["! comment", "O"] = ⟨#[], (#[(0, 0)] : Array (Int32 × Int32)).map cellBits⟩ := by
  decide +kernel

/-- Proof of `plaintext_round_trip_empty`. -/
theorem plaintext_round_trip_empty_Impl :
    deserializePlaintext (serializePlaintext #[] 0 0 0 0) = ⟨#[], #[]⟩ := by
  decide +kernel

/-- Proof of `plaintext_round_trip_glider`. -/
theorem plaintext_round_trip_glider_Impl :
    deserializePlaintext
        (serializePlaintext ((#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits)
          0 2 0 2) =
      ⟨#[], (#[(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ := by
  decide +kernel

/-- Proof of `deserializePlaintext_warnings`. -/
theorem deserializePlaintext_warnings_Impl :
    deserializePlaintext #["O.O", "", "O", "x O"] =
      ⟨#[.blankLine 2, .shortLine 3, .unexpectedChar 4 1 120, .unexpectedChar 4 2 32],
        (#[(0, 0), (2, 0), (0, 1), (0, 2), (2, 2)] : Array (Int32 × Int32)).map cellBits⟩ := by
  decide +kernel

/-- Proof of `deserializePlaintext_non_ascii`. -/
theorem deserializePlaintext_non_ascii_Impl :
    deserializePlaintext #["OéO"] =
      ⟨#[.unexpectedChar 1 2 233], (#[(0, 0), (1, 0), (2, 0)] : Array (Int32 × Int32)).map cellBits⟩ := by
  decide +kernel

end Algorithm

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

import proofs.Life105Proofs

namespace Algorithm

/-!
# Life 1.05 deserialization of any input

`deserializeLife105` is `life105Spec` over the lines: the header, `#D` description lines, an optional `#N` or
`#R` rule line, and then `blocksSpec`: each `#P x y` line starts a block, whose rows of `.` and `*` follow.
-/

/--
What `parseBlocks` gives for lines `ls`, the first of which is line `i + 1` (1-based). `blk` is the current block's
x and y and its next row, if a block has started; `acc` holds the cells read so far.
-/
def blocksSpec : List String → UInt32 → Option (Int32 × Int32 × Int32) → List (Int32 × Int32) →
    Array Life105Warning → Life105Result
  | [], _, _, acc, warns => ⟨.ok, warns, (acc.map cellBits).toArray⟩
  | l :: ls, i, blk, acc, warns =>
    if startsWithHash l.toByteArray 80 then
      match parseBlockHeader l.toByteArray with
      | none => ⟨.unexpectedInput l (i + 1) 3, warns, #[]⟩
      | some c => blocksSpec ls (i + 1) (some (c.x, c.y, 0)) acc warns
    else
      match blk with
      | some (bx, bY, ri) =>
        if isRowLine l.toByteArray then
          blocksSpec ls (i + 1) (some (bx, bY, ri + 1)) (acc ++ rowCells105 l.toByteArray 0 bx (bY + ri)) warns
        else ⟨.unexpectedInput l (i + 1) 1, warns, #[]⟩
      | none => ⟨.unexpectedInput l (i + 1) 1, warns, #[]⟩

/-- What `deserializeLife105` gives for any lines. -/
def life105Spec : List String → Life105Result
  | [] => ⟨.ok, #[.emptyFile], #[]⟩
  | h :: ls =>
    if h ≠ "#Life 1.05" then ⟨.invalidHeader h, #[], #[]⟩
    else
      let rest := ls.dropWhile (fun l => startsWithHash l.toByteArray 68)
      let i : UInt32 := (1 + (ls.length - rest.length)).toUInt32
      match rest with
      | [] => ⟨.ok, #[], #[]⟩
      | r :: rs =>
        if startsWithHash r.toByteArray 78 then
          blocksSpec rs (i + 1) none [] (if r ≠ "#N" then #[.unexpectedInput r (i + 1) 3] else #[])
        else if startsWithHash r.toByteArray 82 then
          if checkRuleLine r.toByteArray = 0 then blocksSpec rs (i + 1) none [] #[]
          else if checkRuleLine r.toByteArray = 1 then ⟨.unexpectedInput r (i + 1) 3, #[], #[]⟩
          else ⟨.ruleNotSupported, #[], #[]⟩
        else blocksSpec (r :: rs) i none [] #[]

theorem isRow105_of_isRowRest (B : ByteArray) (hb : B.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32), B.size - p.toNat = n → isRowRest B B.size.toUInt32 p = true →
      ∀ q (hq : q < B.size), p.toNat ≤ q → B[q] = 46 ∨ B[q] = 42 := by
  intro n
  induction n with
  | zero => intro p hn _ q hq hpq; omega
  | succ n ih =>
    intro p hn hr q hq hpq
    have hlt : p.toNat < B.size := by omega
    have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hb]; exact hlt
    rw [isRowRest] at hr
    simp only [hyes, ↓reduceDIte] at hr
    split at hr
    · rename_i hb'
      by_cases hpq' : q = p.toNat
      · subst hpq'
        rw [byteArray_get!_eq hlt] at hb'
        simpa [Bool.or_eq_true, beq_iff_eq] using hb'
      · exact ih (p + 1) (by have := u32_toNat_succ hlt hb; omega) hr q hq
          (by have := u32_toNat_succ hlt hb; omega)
    · simp at hr

theorem isRow105_of_isRowLine (B : ByteArray) (hb : B.size < 2 ^ 32) (h : isRowLine B = true) : IsRow105 B := by
  unfold isRowLine at h
  rw [Bool.and_eq_true] at h
  intro q hq
  exact isRow105_of_isRowRest B hb _ 0 rfl h.2 q hq (Nat.zero_le _)

theorem parseBlocks_spec (lines : Array String) (hls : lines.size < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (B : ByteArray) (L : UInt32) (hasBlock : Bool) (bx bY ri : Int32)
      (warns : Array Life105Warning) (cells : U64Buf) (acc : List (Int32 × Int32)),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → U64Buf.Rep cells (acc.toArray.map cellBits) →
      acc.length + remBytes (lines.toList.drop i.toNat) < 2 ^ 31 →
      parseBlocks lines lines.size.toUInt32 i false B L 0 hasBlock bx bY ri warns cells =
        blocksSpec (lines.toList.drop i.toNat) i (if hasBlock then some (bx, bY, ri) else none) acc warns := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i B L hasBlock bx bY ri warns cells acc hn hi hc _
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; omega
    rw [parseBlocks]
    simp [hnot, List.drop_eq_nil_of_le (show lines.toList.length ≤ i.toNat by simp; omega), blocksSpec,
      U64Buf.toArray_of_rep hc]
  | succ n ih =>
    intro i B L hasBlock bx bY ri warns cells acc hn hi hc ha
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; exact hlt
    have hsucc := u32_toNat_succ hlt hs32
    have hdrop := toList_drop_eq_cons lines i.toNat hlt
    rw [hdrop, remBytes_cons] at ha
    rw [hdrop]
    have hl! : lines[i.toNat]! = lines[i.toNat] := getElem!_pos lines i.toNat hlt
    generalize hline : lines[i.toNat] = l at hl! ha
    generalize hrest : lines.toList.drop (i.toNat + 1) = rest at ha
    have hrest' : lines.toList.drop (i + 1).toNat = rest := by rw [hsucc, hrest]
    rw [parseBlocks]
    simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hl!, blocksSpec]
    by_cases hP : startsWithHash l.toByteArray 80 = true
    · simp only [hP, ite_true]
      cases hph : parseBlockHeader l.toByteArray with
      | none => simp
      | some c =>
        simp only
        rw [ih (i + 1) _ _ true c.x c.y 0 warns cells acc (by omega) (by omega) hc (by rw [hrest']; omega), hrest']
        simp
    · simp only [hP, Bool.false_eq_true, ite_false]
      cases hasBlock with
      | false => simp
      | true =>
        simp only [Bool.and_true, ite_true]
        by_cases hR : isRowLine l.toByteArray = true
        · simp only [hR, ite_true]
          have hb31 : l.toByteArray.size < 2 ^ 31 := by omega
          obtain ⟨c', hc', heq⟩ := parseBlocks_row lines lines.size.toUInt32 i l.toByteArray
            (isRow105_of_isRowLine _ (by omega) hR) hb31 hyes true bx bY ri warns _ 0 cells acc.toArray rfl
            (by simp) hc (by simp only [List.size_toArray, UInt32.toNat_zero, Nat.sub_zero]; omega)
          rw [heq]
          have hlen := rowCells105_length_le l.toByteArray 0 bx (bY + ri)
          rw [ih (i + 1) _ _ true bx bY (ri + 1) warns c' (acc ++ rowCells105 l.toByteArray 0 bx (bY + ri))
            (by omega) (by omega) (by simpa using hc') (by rw [hrest']; simp; omega), hrest']
          simp
        · simp only [hR, Bool.false_eq_true, ite_false]
          simp

theorem skipDescriptions_spec (lines : Array String) (hs : lines.size < 2 ^ 32) :
    ∀ (n : Nat) (k : UInt32), lines.size - k.toNat = n → k.toNat ≤ lines.size →
      k.toNat ≤ (skipDescriptions lines lines.size.toUInt32 k).toNat ∧
        (skipDescriptions lines lines.size.toUInt32 k).toNat ≤ lines.size ∧
        lines.toList.drop (skipDescriptions lines lines.size.toUInt32 k).toNat =
          (lines.toList.drop k.toNat).dropWhile (fun l => startsWithHash l.toByteArray 68) := by
  intro n
  induction n with
  | zero =>
    intro k hn hk
    have hnot : ¬ k < lines.size.toUInt32 := by rw [u32_lt_size_iff hs]; omega
    rw [skipDescriptions]
    simp [hnot, List.drop_eq_nil_of_le (show lines.toList.length ≤ k.toNat by simp; omega), hk]
  | succ n ih =>
    intro k hn hk
    have hlt : k.toNat < lines.size := by omega
    have hyes : k < lines.size.toUInt32 := by rw [u32_lt_size_iff hs]; exact hlt
    have hsucc := u32_toNat_succ hlt hs
    rw [skipDescriptions]
    simp only [hyes, ↓reduceDIte, getElem!_pos lines k.toNat hlt]
    rw [toList_drop_eq_cons lines k.toNat hlt, List.dropWhile_cons]
    split
    · obtain ⟨h1, h2, h3⟩ := ih (k + 1) (by omega) (by omega)
      rw [hsucc] at h1 h3
      exact ⟨by omega, h2, h3⟩
    · exact ⟨Nat.le_refl _, by omega, toList_drop_eq_cons lines k.toNat hlt⟩

/-- Deserialization of any lines (of fewer than 2 ^ 31 bytes in all) is `life105Spec`. -/
theorem deserializeLife105_eq_spec (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 31) :
    deserializeLife105 lines = life105Spec lines.toList := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  unfold deserializeLife105
  by_cases h0 : lines.size = 0
  · have : lines.toList = [] := by simpa using h0
    simp [h0, this, life105Spec]
  have hne : (lines.size.toUInt32 == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg UInt32.toNat h; rw [u32_size_toNat hs32, UInt32.toNat_zero] at this; omega
  have hpos : 0 < lines.size := by omega
  have hl0 := toList_drop_eq_cons lines 0 hpos
  simp only [List.drop_zero] at hl0
  rw [hl0]
  simp only [hne, Bool.false_eq_true, ite_false, life105Spec, getElem!_pos lines 0 hpos, bne_iff_ne, ne_eq]
  by_cases hH : lines[0] = "#Life 1.05"
  · simp only [hH, not_true_eq_false, ite_false]
    obtain ⟨hj1, hj2, hj3⟩ := skipDescriptions_spec lines hs32 _ 1 rfl (by simp; omega)
    simp only [UInt32.toNat_one] at hj1 hj3
    generalize hj : skipDescriptions lines lines.size.toUInt32 1 = j at hj1 hj2 hj3
    rw [← hj3]
    have hi : (1 + ((lines.toList.drop 1).length - (lines.toList.drop j.toNat).length)).toUInt32 = j := by
      apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by simp; omega)]; simp; omega
    simp only [hi]
    have hbj : ∀ k, remBytes (lines.toList.drop k) ≤ remBytes lines.toList := by
      intro k
      unfold remBytes
      rw [← List.take_append_drop k lines.toList, List.map_append, List.sum_append]
      simp
    by_cases hjl : j < lines.size.toUInt32
    · have hjlt : j.toNat < lines.size := by rw [u32_lt_size_iff hs32] at hjl; exact hjl
      have hjsucc := u32_toNat_succ hjlt hs32
      rw [toList_drop_eq_cons lines j.toNat hjlt]
      simp only [hjl, ite_true, getElem!_pos lines j.toNat hjlt]
      generalize hr : lines[j.toNat] = r
      have hdr : lines.toList.drop (j + 1).toNat = lines.toList.drop (j.toNat + 1) := by rw [hjsucc]
      have hbr := hbj (j.toNat + 1)
      by_cases hN : startsWithHash r.toByteArray 78 = true
      · simp only [hN, ite_true]
        rw [parseBlocks_spec lines hls _ (j + 1) _ _ false 0 0 0 _ U64Buf.empty [] rfl (by omega)
          (by simpa using U64Buf.rep_empty) (by rw [hdr]; simp; omega), hdr]
        simp
      · simp only [hN, Bool.false_eq_true, ite_false]
        by_cases hR : startsWithHash r.toByteArray 82 = true
        · simp only [hR, ite_true]
          by_cases c0 : checkRuleLine r.toByteArray = 0
          · simp only [c0, beq_self_eq_true, ite_true]
            rw [parseBlocks_spec lines hls _ (j + 1) _ _ false 0 0 0 #[] U64Buf.empty [] rfl (by omega)
              (by simpa using U64Buf.rep_empty) (by rw [hdr]; simp; omega), hdr]
            simp
          · have c0' : (checkRuleLine r.toByteArray == 0) = false := by simpa using c0
            simp only [c0, c0', Bool.false_eq_true, ite_false]
            by_cases c1 : checkRuleLine r.toByteArray = 1
            · simp [c1]
            · have c1' : (checkRuleLine r.toByteArray == 1) = false := by simpa using c1
              simp [c1, c1']
        · simp only [hR, Bool.false_eq_true, ite_false]
          have hd := toList_drop_eq_cons lines j.toNat hjlt
          rw [hr] at hd
          rw [parseBlocks_spec lines hls _ j _ _ false 0 0 0 #[] U64Buf.empty [] rfl (by omega)
            (by simpa using U64Buf.rep_empty) (by have := hbj j.toNat; simp; omega), hd]
          simp
    · have hjs : j.toNat = lines.size := by
        have := mt (u32_lt_size_iff hs32).mpr hjl; omega
      rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp [hjl]
  · simp [hH]

end Algorithm

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

import Algorithm.Life105
import proofs.SerialCoreProofs
import proofs.PlaintextProofs

namespace Algorithm

/-! ## Rule lines -/

open Classical in
/--
A `#R survival/birth` line with nonempty digit lists is Conway's rules (0) exactly when the survival digits are
{2, 3} and the birth digits are {3}, and another rule (2) otherwise.
-/
theorem checkRuleLine_digits (s b : List UInt8) (hs : s ≠ []) (hb : b ≠ [])
    (hsd : ∀ d ∈ s, isDigitByte d = true) (hbd : ∀ d ∈ b, isDigitByte d = true)
    (hsz : s.length + b.length + 4 < 2 ^ 32) :
    checkRuleLine ⟨(35 :: 82 :: 32 :: (s ++ 47 :: b)).toArray⟩ =
      if ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b) then 0 else 2 := by
  generalize hL : 35 :: 82 :: 32 :: (s ++ 47 :: b) = L
  have hLlen : L.length = s.length + b.length + 4 := by rw [← hL]; simp; omega
  generalize hB : (⟨L.toArray⟩ : ByteArray) = B
  have hBsize : B.size = L.length := by rw [← hB, size_of_list]
  have hB32 : B.size < 2 ^ 32 := by omega
  have hget : ∀ k, k < L.length → B.get! k = L[k]! := by
    intro k hk
    rw [byteArray_get!_eq (by omega), getElem!_pos L k hk]
    subst hB
    exact byteArray_getElem_of_list L k hk
  have hfrom : ∀ k, bytesFrom B k = L.drop k := by intro k; rw [← hB, bytesFrom_of_list]
  have hlimit : B.size.toUInt32.toNat = L.length := by rw [u32_size_toNat hB32, hBsize]
  unfold checkRuleLine
  have h3 : ¬ B.size.toUInt32 < 3 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; simp; omega
  have g0 : B.get! 0 = 35 := by rw [hget 0 (by omega)]; subst hL; rfl
  have g1 : B.get! 1 = 82 := by rw [hget 1 (by omega)]; subst hL; rfl
  have g2 : B.get! 2 = 32 := by rw [hget 2 (by omega)]; subst hL; rfl
  simp only [h3, decide_false, g0, g1, g2, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false]
  -- The survival digits.
  have hs3 : bytesFrom B (3 : UInt32).toNat = s ++ 47 :: b := by rw [hfrom]; subst hL; rfl
  obtain ⟨he1, hm1⟩ := scanDigitSet_spec B hB32 _ 3 0 rfl (by simp; omega)
  rw [show (3 : UInt32).toNat = 3 from rfl] at hs3 he1 hm1
  rw [hs3, takeWhile_digits_append s _ hsd (by intro y hy; simp at hy; subst hy; exact not_digit_47)] at he1 hm1
  generalize hsc1 : scanDigitSet B B.size.toUInt32 3 0 = r1 at he1 hm1
  obtain ⟨e1, m1⟩ := r1
  simp only at he1 hm1 ⊢
  have hslen : 0 < s.length := List.length_pos_iff.mpr hs
  have hne3 : ¬ (e1 == 3) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); simp at this; omega
  have hlt1 : e1 < B.size.toUInt32 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; omega
  have hslash : B.get! e1.toNat = 47 := by
    rw [hget _ (by omega), he1]; subst hL
    rw [getElem!_pos _ _ (by simp; omega)]
    simp [show 3 + s.length = s.length + 3 by omega, List.getElem_append_right]
  simp only [hne3, decide_true, hlt1, Bool.not_true, hslash, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ite_false]
  -- The birth digits.
  have he1n : e1.toNat = 3 + s.length := he1
  have hsucc : (e1 + 1).toNat = 3 + s.length + 1 := by rw [UInt32.toNat_add, he1n]; simp; omega
  have hb4 : bytesFrom B (e1 + 1).toNat = b ++ [] := by
    rw [hfrom, hsucc]; subst hL
    simp only [List.append_nil]
    rw [show 3 + s.length + 1 = (s.length + 1) + 3 by omega, ← List.drop_drop]
    simp
  obtain ⟨he2, hm2⟩ := scanDigitSet_spec B hB32 _ (e1 + 1) 0 rfl (by rw [hsucc]; omega)
  rw [hb4, takeWhile_digits_append b [] hbd (by simp)] at he2 hm2
  generalize hsc2 : scanDigitSet B B.size.toUInt32 (e1 + 1) 0 = r2 at he2 hm2
  obtain ⟨e2, m2⟩ := r2
  simp only at he2 hm2 ⊢
  have hblen : 0 < b.length := List.length_pos_iff.mpr hb
  have heq : e2 = B.size.toUInt32 := by apply UInt32.toNat_inj.mp; rw [he2, hsucc, hlimit]; omega
  have hne4 : ¬ (B.size.toUInt32 == e1 + 1) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [hlimit, hsucc] at this; omega
  rw [heq]
  simp only [hne4, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [hm1, hm2]
  have hS := digitMask_eq_survival23 s hsd
  have hBi := digitMask_eq_birth3 b hbd
  by_cases hc : ((∀ d ∈ s, d = 50 ∨ d = 51) ∧ 50 ∈ s ∧ 51 ∈ s) ∧ ((∀ d ∈ b, d = 51) ∧ 51 ∈ b)
  · rw [ite_eq_left hc, hS.mpr hc.1, hBi.mpr hc.2]; simp
  · rw [ite_eq_right hc]
    have : ¬ (s.foldl digitMaskStep 0 == survival23Mask && b.foldl digitMaskStep 0 == birth3Mask) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      rintro ⟨h1, h2⟩
      exact hc ⟨hS.mp h1, hBi.mp h2⟩
    rw [ite_eq_right this]

/-! ## Block headers -/

theorem bytes_formatBlockHeader (x y : Int32) :
    (formatBlockHeader x y).toByteArray.data.toList =
      [35, 80, 32] ++ (toString x).toByteArray.data.toList ++ 32 :: (toString y).toByteArray.data.toList := by
  show ("#P " ++ toString x ++ " " ++ toString y).toByteArray.data.toList = _
  simp only [String.toByteArray_append, byteArray_append_toList, List.append_assoc]
  rfl

theorem toString_int32_ne_nil (x : Int32) : (toString x).toByteArray.data.toList ≠ [] := by
  rw [bytes_toString_int32]
  have := (natDigitBytes_spec x.toInt.natAbs).2.2
  split <;> simp_all

/-- Every block header line parses back to its coordinates. -/
theorem parseBlockHeader_format (x y : Int32) :
    parseBlockHeader (formatBlockHeader x y).toByteArray = some ⟨x, y⟩ := by
  generalize hX : (toString x).toByteArray.data.toList = X
  generalize hY : (toString y).toByteArray.data.toList = Y
  have hL := bytes_formatBlockHeader x y
  rw [hX, hY] at hL
  have hXlen : X.length ≤ 11 := hX ▸ bytes_toString_int32_length x
  have hYlen : Y.length ≤ 11 := hY ▸ bytes_toString_int32_length y
  have hYne : Y ≠ [] := hY ▸ toString_int32_ne_nil y
  rw [byteArray_eq_of_toList hL]
  generalize hLL : [35, 80, 32] ++ X ++ 32 :: Y = L
  have hLlen : L.length = X.length + Y.length + 4 := by rw [← hLL]; simp; omega
  have hsize : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  have hB32 : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by omega
  have hlimit : (⟨L.toArray⟩ : ByteArray).size.toUInt32.toNat = L.length := by rw [u32_size_toNat hB32, hsize]
  have hget : ∀ k, k < L.length → (⟨L.toArray⟩ : ByteArray).get! k = L[k]! := get!_of_list L
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  unfold parseBlockHeader
  have h3 : ¬ (⟨L.toArray⟩ : ByteArray).size.toUInt32 < 3 := by rw [UInt32.lt_iff_toNat_lt, hlimit]; simp; omega
  have g0 : (⟨L.toArray⟩ : ByteArray).get! 0 = 35 := by rw [hget 0 (by omega)]; subst hLL; rfl
  have g1 : (⟨L.toArray⟩ : ByteArray).get! 1 = 80 := by rw [hget 1 (by omega)]; subst hLL; rfl
  have g2 : (⟨L.toArray⟩ : ByteArray).get! 2 = 32 := by rw [hget 2 (by omega)]; subst hLL; rfl
  simp only [h3, decide_false, g0, g1, g2, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false]
  -- The first number.
  have hx : parseInt32At ⟨L.toArray⟩ 3 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      some ⟨x, (3 + X.length).toUInt32⟩ := by
    have hp := parseInt32Spec_toString x (32 :: Y) (by intro z hz; simp at hz; subst hz; decide)
    rw [hX] at hp
    rw [parseInt32At_spec _ hB32 3 (by simp; omega), show (3 : UInt32).toNat = 3 from rfl, bytesFrom_of_list,
      ← hLL, show List.drop 3 ([35, 80, 32] ++ X ++ 32 :: Y) = X ++ 32 :: Y by simp, hp, Option.map_some]
    congr 2
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hidx _ (by omega), hidx _ (by omega)]; simp; omega
  rw [hx]
  simp only
  have hlt : (3 + X.length).toUInt32 < (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.lt_iff_toNat_lt, hidx _ (by omega), hlimit]; omega
  have hsp : (⟨L.toArray⟩ : ByteArray).get! (3 + X.length).toUInt32.toNat = 32 := by
    rw [hidx _ (by omega), hget _ (by omega), ← hLL, getElem!_pos _ _ (by simp; omega)]
    rw [List.getElem_append_right (by simp; omega)]
    simp [show 3 + X.length - (X.length + 1 + 1 + 1) = 0 by omega]
  simp only [hlt, decide_true, hsp, beq_self_eq_true, Bool.and_self, ite_true]
  -- The second number.
  have hs2 : (3 + X.length).toUInt32 + 1 = (4 + X.length).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hidx _ (by omega), hidx _ (by omega)]; simp; omega
  rw [hs2]
  have hy : parseInt32At ⟨L.toArray⟩ (4 + X.length).toUInt32 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
      some ⟨y, (⟨L.toArray⟩ : ByteArray).size.toUInt32⟩ := by
    rw [parseInt32At_spec _ hB32 _ (by rw [hidx _ (by omega), hsize]; omega), hidx _ (by omega), bytesFrom_of_list]
    have : L.drop (4 + X.length) = (toString y).toByteArray.data.toList ++ [] := by
      rw [← hLL, List.append_nil, hY, show 4 + X.length = (X.length + 1) + 3 by omega]
      simp only [List.cons_append, List.nil_append, List.drop_succ_cons]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        show X.length + 1 - X.length = 1 by omega]
      rfl
    have hp := parseInt32Spec_toString y [] (by simp)
    rw [this, hp, Option.map_some, hY]
    congr 2
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hidx _ (by omega), hlimit, u32_size_toNat (by omega)]; omega
  rw [hy]
  simp

/-! ## Rows -/

/-- Every byte is `.` or `*`. -/
def IsRow105 (B : ByteArray) : Prop := ∀ (q : Nat) (hq : q < B.size), B[q] = 46 ∨ B[q] = 42

/-- The alive cells of a row with bytes `B`, from byte `p` on, for a row at `y` starting at `x0`. -/
def rowCells105 (B : ByteArray) (p : Nat) (x0 y : Int32) : List (Int32 × Int32) :=
  (List.range' p (B.size - p)).filterMap
    (fun c => if B[c]! = 42 then some (x0 + c.toUInt32.toInt32, y) else none)

theorem rowCells105_of_ge (B : ByteArray) (p : Nat) (x0 y : Int32) (h : B.size ≤ p) : rowCells105 B p x0 y = [] := by
  simp [rowCells105, show B.size - p = 0 by omega]

theorem rowCells105_of_lt (B : ByteArray) (p : Nat) (x0 y : Int32) (h : p < B.size) :
    rowCells105 B p x0 y =
      (if B[p]! = 42 then [(x0 + p.toUInt32.toInt32, y)] else []) ++ rowCells105 B (p + 1) x0 y := by
  unfold rowCells105
  rw [show B.size - p = (B.size - (p + 1)) + 1 by omega, List.range'_succ, List.filterMap_cons]
  split <;> simp_all

theorem parseBlocks_row (lines : Array String) (numLines i : UInt32) (B : ByteArray) (hB : IsRow105 B)
    (hb : B.size < 2 ^ 31) (hi : i < numLines) (hasBlock : Bool) (bx bY ri : Int32) (warns : Array Life105Warning) :
    ∀ (n : Nat) (p : UInt32) (cells : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)),
      B.size - p.toNat = n → p.toNat ≤ B.size → cells.Rep a → a.size + (B.size - p.toNat) < 2 ^ 31 →
      ∃ cells' : GrowBuf (Int32 × Int32), cells'.Rep (a ++ (rowCells105 B p.toNat bx (bY + ri)).toArray) ∧
        parseBlocks lines numLines i true B B.size.toUInt32 p hasBlock bx bY ri warns cells =
        parseBlocks lines numLines (i + 1) false B B.size.toUInt32 0 hasBlock bx bY (ri + 1) warns cells' := by
  have hb32 : B.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro p cells a hn hp hrep ha
    have hnot : ¬ p < B.size.toUInt32 := by rw [u32_lt_size_iff hb32]; omega
    refine ⟨cells, by rw [rowCells105_of_ge B p.toNat bx _ (by omega)]; simpa using hrep, ?_⟩
    rw [parseBlocks]
    simp only [hi, ↓reduceDIte, ite_true, hnot]
  | succ n ih =>
    intro p cells a hn hp hrep ha
    have hlt : p.toNat < B.size := by omega
    have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hb32]; exact hlt
    have hsucc := u32_toNat_succ hlt hb32
    rw [parseBlocks]
    simp only [hi, ↓reduceDIte, ite_true, hyes]
    rw [byteArray_get!_eq hlt, rowCells105_of_lt B p.toNat bx _ hlt, getElem!_pos B p.toNat hlt]
    have hp' : p.toNat.toUInt32 = p := by apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega)]
    rcases hB p.toNat hlt with h46 | h42
    · rw [h46]
      simp only [show ((46 : UInt8) == 42) = false by decide, Bool.false_eq_true, ite_false,
        show ¬ ((46 : UInt8) = 42) by decide, List.nil_append]
      obtain ⟨c', hc', heq⟩ := ih (p + 1) cells a (by omega) (by omega) hrep (by omega)
      rw [hsucc] at hc'
      exact ⟨c', hc', heq⟩
    · rw [h42]
      simp only [show ((42 : UInt8) == 42) = true by decide, ite_true]
      have hpush := GrowBuf.rep_push hrep (bx + p.toInt32, bY + ri) (by omega)
      obtain ⟨c', hc', heq⟩ := ih (p + 1) _ _ (by omega) (by omega) hpush
        (by simp only [Array.size_push]; omega)
      rw [hsucc] at hc'
      refine ⟨c', ?_, heq⟩
      simpa [hp', UInt32.toInt32] using hc'

/-! ## Blocks -/

/-- The grid of a serialized block. -/
def life105Grid (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32) : AsciiBytes :=
  fillGrid cells minX minY 80 (maxY - minY + 1).toUInt32 42 (by decide) 0 cells.size.toUInt32
    (AsciiBytes.replicate (80 * (maxY - minY + 1).toUInt32) 46 (by decide))

/-- Row `r` of a serialized block. -/
def life105Row (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (r : Nat) : String :=
  (life105Grid cells minX minY maxY).toStringRange (r.toUInt32 * 80) (r.toUInt32 * 80 + 80)

theorem serializeLife105Block_eq (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32)
    (hh : (maxY - minY + 1).toUInt32.toNat + 2 < 2 ^ 31) :
    serializeLife105Block cells minX minY maxY =
      #[formatBlockHeader minX minY] ++
        ((List.range (maxY - minY + 1).toUInt32.toNat).map (life105Row cells minX minY maxY)).toArray := by
  unfold serializeLife105Block
  show (gridRows (life105Grid cells minX minY maxY) 80 _ 0 (GrowBuf.empty.push (formatBlockHeader minX minY))).toArray = _
  rw [gridRows_eq _ _ _ hh]
  rfl

/-- The alive cells of a serialized block, row by row. -/
def life105BlockCells (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (r : Nat) : List (Int32 × Int32) :=
  (List.range' r ((maxY - minY + 1).toUInt32.toNat - r)).flatMap
    (fun k => rowCells105 (life105Row cells minX minY maxY k).toByteArray 0 minX (minY + k.toUInt32.toInt32))

theorem life105_row_facts (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (hcs : cells.size < 2 ^ 32)
    (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) (r : Nat) (hr : r < (maxY - minY + 1).toUInt32.toNat) :
    (life105Row cells minX minY maxY r).toByteArray.size = 80 ∧
      IsRow105 (life105Row cells minX minY maxY r).toByteArray := by
  unfold life105Row life105Grid
  generalize hH : (maxY - minY + 1).toUInt32 = H at hwh hr ⊢
  have h80 : (80 : UInt32).toNat = 80 := rfl
  have hg := fillGrid_replicate_spec cells minX minY 80 H 42 46 (by decide) (by decide) hcs (by rw [h80]; omega)
  rw [h80] at hg
  have hrow := toStringRange_row _ 80 H hg.1 (by rw [h80]; omega) r hr
  rw [h80] at hrow
  refine ⟨hrow.1, fun q hq => ?_⟩
  have hq' : q < 80 := by rw [hrow.1] at hq; exact hq
  have := hrow.2 q hq'
  rw [getElem!_pos _ q hq] at this
  rw [this]
  have hk : r * 80 + q < 80 * H.toNat := by
    have : (r + 1) * 80 ≤ H.toNat * 80 := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hg.2 (r * 80 + q) hk]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem isRowRest_of_row (B : ByteArray) (hB : IsRow105 B) (hb : B.size < 2 ^ 32) :
    ∀ (n : Nat) (p : UInt32), B.size - p.toNat = n → isRowRest B B.size.toUInt32 p = true := by
  intro n
  induction n with
  | zero =>
    intro p hn
    have hnot : ¬ p < B.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
    rw [isRowRest]; simp [hnot]
  | succ n ih =>
    intro p hn
    have hlt : p.toNat < B.size := by omega
    have hyes : p < B.size.toUInt32 := by rw [u32_lt_size_iff hb]; exact hlt
    have hsucc := u32_toNat_succ hlt hb
    rw [isRowRest]
    simp only [hyes, ↓reduceDIte, byteArray_get!_eq hlt]
    have : (B[p.toNat] == 46 || B[p.toNat] == 42) = true := by
      rcases hB p.toNat hlt with h | h <;> rw [h] <;> decide
    rw [ite_eq_left this]
    exact ih (p + 1) (by omega)

theorem life105_row_not_header (B : ByteArray) (hB : IsRow105 B) (hs : B.size = 80) :
    startsWithHash B 80 = false ∧ isRowLine B = true := by
  have h0 : B.get! 0 ≠ 35 := by
    rw [byteArray_get!_eq (by omega)]
    rcases hB 0 (by omega) with h | h <;> rw [h] <;> decide
  have hsz : B.size.toUInt32 = 80 := by rw [hs]; rfl
  refine ⟨?_, ?_⟩
  · unfold startsWithHash
    simp [h0]
  · unfold isRowLine
    rw [isRowRest_of_row B hB (by omega) _ 0 rfl, hsz]
    decide

theorem life105BlockCells_of_lt (cells : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (r : Nat)
    (hr : r < (maxY - minY + 1).toUInt32.toNat) :
    life105BlockCells cells minX minY maxY r =
      rowCells105 (life105Row cells minX minY maxY r).toByteArray 0 minX (minY + r.toUInt32.toInt32) ++
        life105BlockCells cells minX minY maxY (r + 1) := by
  unfold life105BlockCells
  rw [show (maxY - minY + 1).toUInt32.toNat - r = ((maxY - minY + 1).toUInt32.toNat - (r + 1)) + 1 by omega,
    List.range'_succ, List.flatMap_cons]

theorem rowCells105_length_le (B : ByteArray) (p : Nat) (x0 y : Int32) : (rowCells105 B p x0 y).length ≤ B.size - p := by
  unfold rowCells105
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem parseBlocks_rows (L : Array String) (hL : L.size < 2 ^ 31) (cs : Array (UInt32 × UInt32))
    (minX minY maxY : Int32) (hcs : cs.size < 2 ^ 32) (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31)
    (i0 : Nat) (hi0 : i0 + 1 ≤ L.size) (rest : List String)
    (hsplit : L.toList.drop (i0 + 1) =
      (List.range (maxY - minY + 1).toUInt32.toNat).map (life105Row cs minX minY maxY) ++ rest) :
    ∀ (n r : Nat) (B : ByteArray) (Lim : UInt32) (warns : Array Life105Warning) (cells : GrowBuf (Int32 × Int32))
      (a : Array (Int32 × Int32)), (maxY - minY + 1).toUInt32.toNat - r = n → r ≤ (maxY - minY + 1).toUInt32.toNat →
      cells.Rep a → a.size + 80 * ((maxY - minY + 1).toUInt32.toNat - r) < 2 ^ 31 →
      ∃ (B' : ByteArray) (Lim' : UInt32) (cells' : GrowBuf (Int32 × Int32)),
        cells'.Rep (a ++ (life105BlockCells cs minX minY maxY r).toArray) ∧
        parseBlocks L L.size.toUInt32 (i0 + 1 + r).toUInt32 false B Lim 0 true minX minY r.toUInt32.toInt32 warns
            cells =
          parseBlocks L L.size.toUInt32 (i0 + 1 + (maxY - minY + 1).toUInt32.toNat).toUInt32 false B' Lim' 0 true minX
            minY (maxY - minY + 1).toUInt32.toNat.toUInt32.toInt32 warns cells' := by
  generalize hH : (maxY - minY + 1).toUInt32.toNat = H at hwh hsplit ⊢
  have hlen : i0 + 1 + H ≤ L.size := by
    have := congrArg List.length hsplit
    rw [List.length_drop, Array.length_toList, List.length_append, List.length_map, List.length_range] at this
    omega
  have hL32 : L.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro r B Lim warns cells a hn hr hrep ha
    have : r = H := by omega
    subst this
    exact ⟨B, Lim, cells, by unfold life105BlockCells; rw [hH]; simpa using hrep, rfl⟩
  | succ n ih =>
    intro r B Lim warns cells a hn hr hrep ha
    have hrH : r < H := by omega
    have hj : i0 + 1 + r < L.size := by omega
    have hjU : (i0 + 1 + r).toUInt32.toNat = i0 + 1 + r := u32_size_toNat (by omega)
    have hline : L[(i0 + 1 + r).toUInt32.toNat]! = life105Row cs minX minY maxY r := by
      rw [hjU, array_getElem!_of_drop L (i0 + 1) r _ rest hsplit (by simp; omega)]
      rw [getElem!_pos _ _ (by simp; omega)]
      simp
    obtain ⟨hsz, hrow⟩ := life105_row_facts cs minX minY maxY hcs (by rw [hH]; exact hwh) r (by rw [hH]; exact hrH)
    obtain ⟨hnh, hisrow⟩ := life105_row_not_header _ hrow hsz
    have hyes : (i0 + 1 + r).toUInt32 < L.size.toUInt32 := by rw [u32_lt_size_iff hL32, hjU]; exact hj
    rw [parseBlocks]
    simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hline, hnh, hisrow, Bool.and_self, ite_true]
    obtain ⟨c', hc', heq⟩ := parseBlocks_row L L.size.toUInt32 (i0 + 1 + r).toUInt32 _ hrow (by omega) hyes true minX
      minY r.toUInt32.toInt32 warns _ 0 cells a rfl (by simp) hrep (by
        have h1 : 1 ≤ H - r := by omega
        have : 80 * 1 ≤ 80 * (H - r) := Nat.mul_le_mul_left 80 h1
        rw [hsz, UInt32.toNat_zero]; omega)
    rw [heq]
    have hnext : (i0 + 1 + r).toUInt32 + 1 = (i0 + 1 + (r + 1)).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hjU, u32_size_toNat (by omega)]; simp; omega
    have hri : r.toUInt32.toInt32 + 1 = (r + 1).toUInt32.toInt32 := by
      have : (r + 1).toUInt32 = r.toUInt32 + 1 := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, Nat.toUInt32_eq, Nat.toUInt32_eq, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
        simp
      rw [this]; rfl
    rw [hnext, hri]
    simp only [UInt32.toNat_zero] at hc'
    obtain ⟨B', Lim', c'', hc'', heq'⟩ := ih (r + 1) _ _ warns c' _ (by omega) (by omega) hc' (by
      have h1 := rowCells105_length_le (life105Row cs minX minY maxY r).toByteArray 0 minX
        (minY + r.toUInt32.toInt32)
      rw [hsz] at h1
      have : 80 * (H - r) = 80 * (H - (r + 1)) + 80 := by
        rw [show H - r = (H - (r + 1)) + 1 by omega, Nat.mul_add]
      rw [Array.size_append, List.size_toArray]
      have := @Array.length_toList _ a
      have := @List.size_toArray _
        (rowCells105 (life105Row cs minX minY maxY r).toByteArray 0 minX (minY + r.toUInt32.toInt32))
      omega)
    refine ⟨B', Lim', c'', ?_, heq'⟩
    rw [life105BlockCells_of_lt cs minX minY maxY r (by rw [hH]; exact hrH)]
    simpa [Array.append_assoc] using hc''

theorem startsWithHash_formatBlockHeader (x y : Int32) :
    startsWithHash (formatBlockHeader x y).toByteArray 80 = true := by
  have hL := bytes_formatBlockHeader x y
  rw [byteArray_eq_of_toList hL]
  generalize hLL : [35, 80, 32] ++ (toString x).toByteArray.data.toList ++ 32 :: (toString y).toByteArray.data.toList = L
  have hX := bytes_toString_int32_length x
  have hY := bytes_toString_int32_length y
  have hlen : 4 ≤ L.length ∧ L.length < 2 ^ 32 := by
    rw [← hLL]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hsz : (⟨L.toArray⟩ : ByteArray).size = L.length := size_of_list L
  unfold startsWithHash
  rw [get!_of_list L 0 (by omega), get!_of_list L 1 (by omega)]
  have h0 : L[0]! = 35 := by rw [← hLL]; rfl
  have h1 : L[1]! = 80 := by rw [← hLL]; rfl
  have : (2 : UInt32) ≤ (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    rw [UInt32.le_iff_toNat_le, u32_size_toNat (by rw [hsz]; exact hlen.2), hsz]; simp; omega
  simp [h0, h1, this]

/-- Reading a serialized block adds its alive cells, and leaves the reader after its last row. -/
theorem parseBlocks_block (L : Array String) (hL : L.size < 2 ^ 31) (cs : Array (UInt32 × UInt32))
    (minX minY maxY : Int32) (hcs : cs.size < 2 ^ 32) (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31)
    (i0 : Nat) (rest : List String) (hsplit : L.toList.drop i0 = (serializeLife105Block cs minX minY maxY).toList ++ rest)
    (hasBlock : Bool) (bx bY ri : Int32) (B : ByteArray) (Lim : UInt32) (warns : Array Life105Warning)
    (cells : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)) (hrep : cells.Rep a)
    (ha : a.size + 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    ∃ (B' : ByteArray) (Lim' : UInt32) (cells' : GrowBuf (Int32 × Int32)),
      cells'.Rep (a ++ (life105BlockCells cs minX minY maxY 0).toArray) ∧
      parseBlocks L L.size.toUInt32 i0.toUInt32 false B Lim 0 hasBlock bx bY ri warns cells =
        parseBlocks L L.size.toUInt32 (i0 + 1 + (maxY - minY + 1).toUInt32.toNat).toUInt32 false B' Lim' 0 true minX
          minY (maxY - minY + 1).toUInt32.toNat.toUInt32.toInt32 warns cells' := by
  have hH : (maxY - minY + 1).toUInt32.toNat + 2 < 2 ^ 31 := by omega
  rw [serializeLife105Block_eq cs minX minY maxY hH] at hsplit
  simp only [Array.toList_append, List.singleton_append] at hsplit
  have hL32 : L.size < 2 ^ 32 := by omega
  have hi0 : i0 < L.size := by
    have := congrArg List.length hsplit
    rw [List.length_drop, Array.length_toList] at this
    simp at this; omega
  have hiU : i0.toUInt32.toNat = i0 := u32_size_toNat (by omega)
  have hline : L[i0.toUInt32.toNat]! = formatBlockHeader minX minY := by
    rw [hiU, show i0 = i0 + 0 by rfl, array_getElem!_of_drop L i0 0 [formatBlockHeader minX minY] _
      (by rw [hsplit]; rfl) (by simp)]
    rfl
  have hyes : i0.toUInt32 < L.size.toUInt32 := by rw [u32_lt_size_iff hL32, hiU]; exact hi0
  rw [parseBlocks]
  simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, hline, startsWithHash_formatBlockHeader, ite_true,
    parseBlockHeader_format]
  have hnext : i0.toUInt32 + 1 = (i0 + 1 + 0).toUInt32 := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hiU, u32_size_toNat (by omega)]; simp; omega
  rw [hnext, show (0 : Int32) = (0 : Nat).toUInt32.toInt32 from rfl]
  have hdrop : L.toList.drop (i0 + 1) =
      (List.range (maxY - minY + 1).toUInt32.toNat).map (life105Row cs minX minY maxY) ++ rest := by
    rw [← List.drop_drop, hsplit]; simp
  exact parseBlocks_rows L hL cs minX minY maxY hcs hwh i0 (by omega) rest hdrop _ 0 _ _ warns cells a rfl
    (by omega) hrep (by omega)

/-! ## Files of blocks -/

/-- A block to serialize: its cells (as `cellBits`), `minX`, `minY` and `maxY`. -/
abbrev Life105Block := Array (UInt32 × UInt32) × Int32 × Int32 × Int32

/-- The height of a block. -/
def Life105Block.height (b : Life105Block) : Nat := (b.2.2.2 - b.2.2.1 + 1).toUInt32.toNat

/-- The lines of a serialized block. -/
def Life105Block.lines (b : Life105Block) : List String := (serializeLife105Block b.1 b.2.1 b.2.2.1 b.2.2.2).toList

/-- The alive cells of a serialized block. -/
def Life105Block.cells (b : Life105Block) : List (Int32 × Int32) := life105BlockCells b.1 b.2.1 b.2.2.1 b.2.2.2 0

theorem life105BlockCells_length_le (cs : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (hcs : cs.size < 2 ^ 32)
    (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    ∀ r, (life105BlockCells cs minX minY maxY r).length ≤ 80 * ((maxY - minY + 1).toUInt32.toNat - r) := by
  intro r
  induction h : (maxY - minY + 1).toUInt32.toNat - r generalizing r with
  | zero =>
    unfold life105BlockCells; rw [h]; simp
  | succ n ih =>
    have hr : r < (maxY - minY + 1).toUInt32.toNat := by omega
    rw [life105BlockCells_of_lt cs minX minY maxY r hr, List.length_append]
    have h1 := rowCells105_length_le (life105Row cs minX minY maxY r).toByteArray 0 minX (minY + r.toUInt32.toInt32)
    rw [(life105_row_facts cs minX minY maxY hcs hwh r hr).1] at h1
    have h2 := ih (r + 1) (by omega)
    omega

theorem Life105Block.lines_length (b : Life105Block) (hh : b.height + 2 < 2 ^ 31) :
    b.lines.length = b.height + 1 := by
  unfold Life105Block.lines Life105Block.height at *
  rw [serializeLife105Block_eq _ _ _ _ hh]
  simp

theorem parseBlocks_blocks (L : Array String) (hL : 80 * L.size < 2 ^ 31) (warns : Array Life105Warning) :
    ∀ (bs : List Life105Block) (i0 : Nat) (hasBlock : Bool) (bx bY ri : Int32) (B : ByteArray) (Lim : UInt32)
      (cells : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)),
      (∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31) → i0 ≤ L.size →
      L.toList.drop i0 = bs.flatMap Life105Block.lines → cells.Rep a →
      a.size + 80 * (L.size - i0) < 2 ^ 31 →
      parseBlocks L L.size.toUInt32 i0.toUInt32 false B Lim 0 hasBlock bx bY ri warns cells =
        ⟨0, "", 0, 0, warns, a ++ (bs.flatMap Life105Block.cells).toArray⟩ := by
  have hL32 : L.size < 2 ^ 32 := by omega
  intro bs
  induction bs with
  | nil =>
    intro i0 hasBlock bx bY ri B Lim cells a _ hi0 hsplit hrep _
    have hge : L.size ≤ i0 := by
      have := congrArg List.length hsplit
      rw [List.length_drop, Array.length_toList] at this
      simp at this; omega
    have hnot : ¬ i0.toUInt32 < L.size.toUInt32 := by
      rw [u32_lt_size_iff hL32, u32_size_toNat (by omega)]; omega
    rw [parseBlocks]
    simp only [hnot, ↓reduceDIte, hrep.2.2.2, List.flatMap_nil]
    simp
  | cons blk bs ih =>
    intro i0 hasBlock bx bY ri B Lim cells a hcs hi0 hsplit hrep ha
    obtain ⟨cs, minX, minY, maxY⟩ := blk
    obtain ⟨hcs1, hwh⟩ := hcs (cs, minX, minY, maxY) (by simp)
    unfold Life105Block.height at hwh
    simp only at hwh
    have hl := Life105Block.lines_length (cs, minX, minY, maxY) (by unfold Life105Block.height; simp only; omega)
    unfold Life105Block.lines Life105Block.height at hl
    simp only at hl
    have hsplit' : L.toList.drop i0 =
        (serializeLife105Block cs minX minY maxY).toList ++ bs.flatMap Life105Block.lines := by
      rw [hsplit, List.flatMap_cons]; rfl
    generalize hH : (maxY - minY + 1).toUInt32.toNat = H at hwh hl
    have hfit : i0 + (H + 1) ≤ L.size := by
      have := congrArg List.length hsplit'
      rw [List.length_drop, Array.length_toList, List.length_append, hl] at this
      omega
    obtain ⟨B', Lim', c', hc', heq⟩ := parseBlocks_block L (by omega) cs minX minY maxY hcs1 (by rw [hH]; exact hwh)
      i0 _ hsplit' hasBlock bx bY ri B Lim warns cells a hrep (by rw [hH]; omega)
    rw [heq]
    have hlen := life105BlockCells_length_le cs minX minY maxY hcs1 (by rw [hH]; exact hwh) 0
    rw [hH, Nat.sub_zero] at hlen
    have hdrop : L.toList.drop (i0 + 1 + (maxY - minY + 1).toUInt32.toNat) = bs.flatMap Life105Block.lines := by
      rw [hH, show i0 + 1 + H = i0 + (H + 1) by omega, ← List.drop_drop, hsplit', ← hl]
      simp
    rw [ih _ true minX minY _ B' Lim' c' _ (fun b hb => hcs b (by simp [hb])) (by rw [hH]; omega) hdrop hc' (by
      rw [hH, Array.size_append, List.size_toArray]
      have : 80 * (L.size - i0) = 80 * (L.size - (i0 + 1 + H)) + 80 * (H + 1) := by
        rw [← Nat.mul_add]; congr 1; omega
      have := @Array.length_toList _ a
      have := @List.size_toArray _ (life105BlockCells cs minX minY maxY 0)
      omega)]
    simp [Life105Block.cells, Array.append_assoc]

/--
A `#Life 1.05` file of serialized blocks deserializes, with no warnings, to the alive cells of the blocks, block by
block and row by row.
-/
theorem deserializeLife105_blocks (bs : List Life105Block) (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray) =
      ⟨0, "", 0, 0, #[], (bs.flatMap Life105Block.cells).toArray⟩ := by
  generalize hL : #["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray = L
  have hLsize : L.size = (bs.flatMap Life105Block.lines).length + 2 := by rw [← hL]; simp
  have hL32 : L.size < 2 ^ 32 := by omega
  have h0 : L[0]! = "#Life 1.05" := by rw [← hL, getElem!_pos _ 0 (by simp)]; simp
  have h1 : L[(1 : UInt32).toNat]! = "#N" := by rw [← hL, getElem!_pos _ _ (by simp)]; simp
  unfold deserializeLife105
  have hne : ¬ (L.size.toUInt32 == 0) = true := by
    intro h; have := congrArg UInt32.toNat (beq_iff_eq.mp h)
    rw [u32_size_toNat hL32, UInt32.toNat_zero] at this; omega
  have h1lt : (1 : UInt32) < L.size.toUInt32 := by rw [u32_lt_size_iff hL32]; simp; omega
  have hskip : skipDescriptions L L.size.toUInt32 1 = 1 := by
    rw [skipDescriptions]
    simp only [h1lt, ↓reduceDIte, h1]
    rw [ite_eq_right (by decide)]
  have hN : startsWithHash "#N".toByteArray 78 = true := by decide
  simp only [hne, Bool.false_eq_true, ite_false, h0, bne_self_eq_false, hskip, h1lt, ite_true, h1, hN]
  rw [show (1 : UInt32) + 1 = (2 : Nat).toUInt32 from rfl]
  rw [parseBlocks_blocks L (by omega) #[] bs 2 false 0 0 0 _ 0 GrowBuf.empty #[] hbs (by omega)
    (by rw [← hL]; simp) GrowBuf.rep_empty (by simp; omega)]
  simp

theorem mem_rowCells105 (B : ByteArray) (x0 y : Int32) (q : Int32 × Int32) :
    q ∈ rowCells105 B 0 x0 y ↔ ∃ c, c < B.size ∧ B[c]! = 42 ∧ q = (x0 + c.toUInt32.toInt32, y) := by
  unfold rowCells105
  simp only [List.mem_filterMap, List.mem_range'_1, Nat.zero_add, Nat.sub_zero]
  constructor
  · rintro ⟨c, ⟨-, hc⟩, hq⟩
    split at hq
    · rename_i h42; simp only [Option.some.injEq] at hq; exact ⟨c, hc, h42, hq.symm⟩
    · simp at hq
  · rintro ⟨c, hc, h42, rfl⟩
    exact ⟨c, ⟨Nat.zero_le _, hc⟩, by simp [h42]⟩

/-- The alive cells of a block are exactly its cells inside the block. -/
theorem mem_life105BlockCells (cs : Array (UInt32 × UInt32)) (minX minY maxY : Int32) (hcs : cs.size < 2 ^ 32)
    (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) (q : Int32 × Int32) :
    q ∈ life105BlockCells cs minX minY maxY 0 ↔
      ∃ c ∈ cs, (gridIndex minX minY 80 (maxY - minY + 1).toUInt32 (c.1.toInt32, c.2.toInt32)).isSome ∧
        q = (c.1.toInt32, c.2.toInt32) := by
  have hrowf := life105_row_facts cs minX minY maxY hcs hwh
  unfold life105BlockCells
  simp only [List.mem_flatMap, List.mem_range'_1, Nat.zero_add, Nat.sub_zero, mem_rowCells105]
  unfold life105Row life105Grid at *
  generalize hH : (maxY - minY + 1).toUInt32 = H at hwh hrowf ⊢
  have h80 : (80 : UInt32).toNat = 80 := rfl
  have hg := fillGrid_replicate_spec cs minX minY 80 H 42 46 (by decide) (by decide) hcs (by rw [h80]; omega)
  rw [h80] at hg
  generalize hG : fillGrid cs minX minY 80 H 42 _ 0 cs.size.toUInt32 (AsciiBytes.replicate (80 * H) 46 _) = g
    at hg hrowf ⊢
  have hrow := fun r hr => toStringRange_row g 80 H hg.1 (by rw [h80]; omega) r hr
  simp only [h80] at hrow
  constructor
  · rintro ⟨r, ⟨-, hr⟩, col, hcol, h42, rfl⟩
    rw [(hrow r hr).1] at hcol
    rw [(hrow r hr).2 col hcol] at h42
    have hk : r * 80 + col < 80 * H.toNat := by
      have : (r + 1) * 80 ≤ H.toNat * 80 := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hg.2 _ hk] at h42
    split at h42
    · rename_i hex
      obtain ⟨cell, hcell, hidx⟩ := hex
      obtain ⟨-, -, hrr, hcc⟩ := (gridIndex_eq_iff (w := 80) (by rw [h80]; exact hcol)).mp (by rw [h80]; exact hidx)
      refine ⟨cell, hcell, by rw [hidx]; rfl, ?_⟩
      have h1 : col.toUInt32 = (cell.1.toInt32 - minX).toUInt32 := by
        apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by omega), hcc]
      have h2 : r.toUInt32 = (cell.2.toInt32 - minY).toUInt32 := by
        apply UInt32.toNat_inj.mp; rw [u32_size_toNat (by have := UInt32.toNat_lt H; omega), hrr]
      rw [h1, h2]
      simp only [Int32.toInt32_toUInt32]
      rw [Int32.add_comm minX, Int32.sub_add_cancel, Int32.add_comm minY, Int32.sub_add_cancel]
    · simp at h42
  · rintro ⟨cell, hcell, hsome, rfl⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
    unfold gridIndex at hk
    split at hk
    · rename_i hin
      dsimp only at hin hk
      simp only [Option.some.injEq] at hk
      have hx := UInt32.lt_iff_toNat_lt.mp hin.1
      have hy := UInt32.lt_iff_toNat_lt.mp hin.2
      rw [h80] at hx
      refine ⟨(cell.2.toInt32 - minY).toUInt32.toNat, ⟨Nat.zero_le _, hy⟩, (cell.1.toInt32 - minX).toUInt32.toNat,
        by rw [(hrow _ hy).1]; exact hx, ?_, ?_⟩
      · rw [(hrow _ hy).2 _ hx]
        have hk' : (cell.2.toInt32 - minY).toUInt32.toNat * 80 + (cell.1.toInt32 - minX).toUInt32.toNat < 80 * H.toNat := by
          have : ((cell.2.toInt32 - minY).toUInt32.toNat + 1) * 80 ≤ H.toNat * 80 := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [hg.2 _ hk', ite_eq_left ⟨cell, hcell, by unfold gridIndex; rw [ite_eq_left hin, h80]⟩]
      · simp only [UInt32.ofNat_toNat, Int32.toInt32_toUInt32]
        rw [Int32.add_comm minX, Int32.sub_add_cancel, Int32.add_comm minY, Int32.sub_add_cancel]
    · simp at hk

/--
Round trip: a file of serialized blocks deserializes, with no warnings, to exactly the cells of the blocks that are
inside their block (the 80 columns from `minX`, and the rows from `minY` to `maxY`).
-/
theorem life105_round_trip (bs : List Life105Block) (hbs : ∀ b ∈ bs, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31)
    (hsz : 80 * ((bs.flatMap Life105Block.lines).length + 2) < 2 ^ 31) :
    let r := deserializeLife105 (#["#Life 1.05", "#N"] ++ (bs.flatMap Life105Block.lines).toArray)
    r.status = 0 ∧ r.warnings = #[] ∧
      ∀ q, q ∈ r.cells ↔ ∃ b ∈ bs, ∃ c ∈ b.1,
        (gridIndex b.2.1 b.2.2.1 80 (b.2.2.2 - b.2.2.1 + 1).toUInt32 (c.1.toInt32, c.2.toInt32)).isSome ∧
          q = (c.1.toInt32, c.2.toInt32) := by
  simp only [deserializeLife105_blocks bs hbs hsz]
  refine ⟨trivial, trivial, fun q => ?_⟩
  simp only [List.mem_toArray, List.mem_flatMap]
  constructor
  · rintro ⟨⟨cs, minX, minY, maxY⟩, hb, hq⟩
    obtain ⟨h1, h2⟩ := hbs _ hb
    exact ⟨_, hb, (mem_life105BlockCells cs minX minY maxY h1 h2 q).mp hq⟩
  · rintro ⟨⟨cs, minX, minY, maxY⟩, hb, hc⟩
    obtain ⟨h1, h2⟩ := hbs _ hb
    exact ⟨_, hb, (mem_life105BlockCells cs minX minY maxY h1 h2 q).mpr hc⟩

end Algorithm

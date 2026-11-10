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
# Life 1.05 serialization of whole patterns

`serializeLife105` covers the cells with blocks of 80 columns. Its round trip gives back exactly the cells.
-/

/-- One step of `life105Bounds`. -/
def boundsStep (b : Int32 × Int32 × Int32) (k : UInt64) : Int32 × Int32 × Int32 :=
  let x := (cellKeyX k).toInt32
  let y := (cellKeyY k).toInt32
  (if x < b.1 then x else b.1, if y < b.2.1 then y else b.2.1, if b.2.2 < y then y else b.2.2)

theorem life105Bounds_eq (cells : Array UInt64) (hc : cells.size < 2 ^ 32) :
    ∀ (n : Nat) (i : UInt32) (b : Int32 × Int32 × Int32), cells.size - i.toNat = n → i.toNat ≤ cells.size →
      life105Bounds cells i cells.size.toUInt32 b.1 b.2.1 b.2.2 = (cells.toList.drop i.toNat).foldl boundsStep b := by
  intro n
  induction n with
  | zero =>
    intro i b hn hi
    have hnot : ¬ i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc]; omega
    rw [life105Bounds]
    simp [hnot, List.drop_eq_nil_of_le (show cells.toList.length ≤ i.toNat by simp; omega)]
  | succ n ih =>
    intro i b hn hi
    have hlt : i.toNat < cells.size := by omega
    have hyes : i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc]; exact hlt
    have hsucc := u32_toNat_succ hlt hc
    rw [life105Bounds]
    simp only [hyes, ↓reduceDIte, getElem!_pos cells i.toNat hlt, toList_drop_eq_cons cells i.toNat hlt,
      List.foldl_cons]
    have := ih (i + 1) (boundsStep b cells[i.toNat]) (by omega) (by omega)
    rw [hsucc] at this
    exact this

theorem life105Rest_spec (cells : Array UInt64) (hc : cells.size < 2 ^ 31) (minX : Int32) :
    ∀ (n : Nat) (i : UInt32) (acc : U64Buf) (a : Array UInt64), cells.size - i.toNat = n → i.toNat ≤ cells.size →
      U64Buf.Rep acc a → a.size + (cells.size - i.toNat) < 2 ^ 31 →
      U64Buf.Rep (life105Rest cells minX i cells.size.toUInt32 acc)
        (a ++ ((cells.toList.drop i.toNat).filter (fun k => !inLife105Block minX k)).toArray) := by
  have hc32 : cells.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i acc a hn hi hrep _
    have hnot : ¬ i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc32]; omega
    rw [life105Rest]
    simpa [hnot, List.drop_eq_nil_of_le (show cells.toList.length ≤ i.toNat by simp; omega)] using hrep
  | succ n ih =>
    intro i acc a hn hi hrep ha
    have hlt : i.toNat < cells.size := by omega
    have hyes : i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc32]; exact hlt
    have hsucc := u32_toNat_succ hlt hc32
    rw [life105Rest]
    simp only [hyes, ↓reduceDIte, getElem!_pos cells i.toNat hlt]
    rw [toList_drop_eq_cons cells i.toNat hlt, List.filter_cons]
    by_cases hin : inLife105Block minX cells[i.toNat] = true
    · simp only [hin, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
      have := ih (i + 1) acc a (by omega) (by omega) hrep (by omega)
      rwa [hsucc] at this
    · simp only [hin, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
      have := ih (i + 1) _ _ (by omega) (by omega) (U64Buf.rep_push hrep cells[i.toNat] (by omega))
        (by simp only [Array.size_push]; omega)
      rw [hsucc] at this
      simpa using this

/-- The blocks that `serializeLife105.loop` writes for `cells`, with at most `n` blocks. -/
def life105Split : Nat → Array UInt64 → List Life105Block
  | 0, _ => []
  | n + 1, cells =>
    if cells.size = 0 then []
    else
      let k := cells[0]!
      let b := life105Bounds cells 1 cells.size.toUInt32 (cellKeyX k).toInt32 (cellKeyY k).toInt32
        (cellKeyY k).toInt32
      (cells, b.1, b.2.1, b.2.2) ::
        life105Split n (U64Buf.toArray (life105Rest cells b.1 0 cells.size.toUInt32 U64Buf.empty))

theorem serializeLife105_loop_spec :
    ∀ (n : Nat) (fuel : UInt32) (cells : Array UInt64) (block : Array String) (j : UInt32) (acc : GrowBuf String)
      (a : Array String),
      fuel.toNat = n → cells.size < 2 ^ 31 → block.size < 2 ^ 32 → j.toNat ≤ block.size → acc.Rep a →
      a.size + (block.size - j.toNat) + ((life105Split n cells).flatMap Life105Block.lines).length < 2 ^ 31 →
      (serializeLife105.loop fuel cells block j acc).Rep
        (a ++ (block.toList.drop j.toNat ++ (life105Split n cells).flatMap Life105Block.lines).toArray) := by
  intro n
  induction n with
  | zero =>
    intro fuel cells block j acc a hf _ hb hj hrep ha
    have hf0 : fuel = 0 := UInt32.toNat_inj.mp (by simpa using hf)
    induction hm : block.size - j.toNat generalizing j acc a with
    | zero =>
      have hnot : ¬ j < block.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
      rw [serializeLife105.loop]
      simp only [hnot, ↓reduceDIte, hf0]
      simpa [life105Split, List.drop_eq_nil_of_le (show block.toList.length ≤ j.toNat by simp; omega)] using hrep
    | succ m ihm =>
      have hlt : j.toNat < block.size := by omega
      have hyes : j < block.size.toUInt32 := by rw [u32_lt_size_iff hb]; exact hlt
      have hsucc := u32_toNat_succ hlt hb
      rw [serializeLife105.loop]
      simp only [hyes, ↓reduceDIte, getElem!_pos block j.toNat hlt]
      have := ihm (j + 1) (acc.push block[j.toNat]) (a.push block[j.toNat]) (by omega)
        (GrowBuf.rep_push hrep _ (by omega)) (by simp only [Array.size_push]; omega) (by omega)
      rw [hsucc] at this
      rw [toList_drop_eq_cons block j.toNat hlt]
      simpa using this
  | succ n ih =>
    intro fuel cells block j acc a hf hc hb hj hrep ha
    have hf0 : fuel ≠ 0 := by intro h; subst h; simp at hf
    have hc32 : cells.size < 2 ^ 32 := by omega
    induction hm : block.size - j.toNat generalizing j acc a with
    | succ m ihm =>
      have hlt : j.toNat < block.size := by omega
      have hyes : j < block.size.toUInt32 := by rw [u32_lt_size_iff hb]; exact hlt
      have hsucc := u32_toNat_succ hlt hb
      rw [serializeLife105.loop]
      simp only [hyes, ↓reduceDIte, getElem!_pos block j.toNat hlt]
      have := ihm (j + 1) (acc.push block[j.toNat]) (a.push block[j.toNat]) (by omega)
        (GrowBuf.rep_push hrep _ (by omega)) (by simp only [Array.size_push]; omega) (by omega)
      rw [hsucc] at this
      rw [toList_drop_eq_cons block j.toNat hlt]
      simpa using this
    | zero =>
      have hnot : ¬ j < block.size.toUInt32 := by rw [u32_lt_size_iff hb]; omega
      have hdrop : block.toList.drop j.toNat = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [serializeLife105.loop]
      simp only [hnot, ↓reduceDIte, hf0, hdrop, List.nil_append]
      by_cases h0 : cells.size = 0
      · have : (cells.size.toUInt32 == 0) = true := by rw [h0]; rfl
        simp only [this, ite_true]
        simpa [life105Split, h0] using hrep
      · have : (cells.size.toUInt32 == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro h
          have := congrArg UInt32.toNat h; rw [u32_size_toNat hc32, UInt32.toNat_zero] at this; omega
        simp only [this, Bool.false_eq_true, ite_false]
        simp only [life105Split, h0, ite_false, List.flatMap_cons, List.length_append] at ha ⊢
        generalize life105Bounds cells 1 cells.size.toUInt32 (cellKeyX cells[0]!).toInt32
          (cellKeyY cells[0]!).toInt32 (cellKeyY cells[0]!).toInt32 = B at ha ⊢
        have hlines : Life105Block.lines (cells, B.1, B.2.1, B.2.2) =
            (serializeLife105Block cells B.1 B.2.1 B.2.2).toList := rfl
        rw [hlines] at ha ⊢
        generalize serializeLife105Block cells B.1 B.2.1 B.2.2 = blk at ha ⊢
        have hrest := life105Rest_spec cells hc B.1 _ 0 U64Buf.empty #[] rfl (by simp) U64Buf.rep_empty
          (by simp; omega)
        generalize life105Rest cells B.1 0 cells.size.toUInt32 U64Buf.empty = R at hrest ha ⊢
        have hRsz : (U64Buf.toArray R).size < 2 ^ 31 := by
          rw [U64Buf.toArray_of_rep hrest]
          have := List.length_filter_le (fun k => !inLife105Block B.1 k) (cells.toList.drop 0)
          simp at this ⊢; omega
        have hfuel : (fuel - 1).toNat = n := by
          rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp; omega
        have hblk : blk.size < 2 ^ 32 := by simp at ha; omega
        have := ih (fuel - 1) (U64Buf.toArray R) blk 0 acc a hfuel hRsz hblk (by simp) hrep
          (by simp at ha ⊢; omega)
        simpa using this

/-- What `life105Bounds` gives, from the bounds `b` and the cells `l`. -/
theorem foldl_boundsStep (l : List UInt64) : ∀ (b : Int32 × Int32 × Int32),
    let r := l.foldl boundsStep b
    r.1.toInt ≤ b.1.toInt ∧ r.2.1.toInt ≤ b.2.1.toInt ∧ b.2.2.toInt ≤ r.2.2.toInt ∧
      (∀ k ∈ l, r.1.toInt ≤ (keyCell k).1.toInt ∧ r.2.1.toInt ≤ (keyCell k).2.toInt ∧
        (keyCell k).2.toInt ≤ r.2.2.toInt) ∧
      (r.1 = b.1 ∨ ∃ k ∈ l, (keyCell k).1 = r.1) ∧ (r.2.1 = b.2.1 ∨ ∃ k ∈ l, (keyCell k).2 = r.2.1) ∧
      (r.2.2 = b.2.2 ∨ ∃ k ∈ l, (keyCell k).2 = r.2.2) := by
  induction l with
  | nil => intro b; simp
  | cons k ks ih =>
    intro b
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (boundsStep b k)
    generalize ks.foldl boundsStep (boundsStep b k) = r at h1 h2 h3 h4 h5 h6 h7 ⊢
    have ex : (keyCell k).1 = (cellKeyX k).toInt32 := rfl
    have ey : (keyCell k).2 = (cellKeyY k).toInt32 := rfl
    simp only [boundsStep] at h1 h2 h3 h5 h6 h7
    generalize (cellKeyX k).toInt32 = x at h1 h5 ex
    generalize (cellKeyY k).toInt32 = y at h2 h3 h6 h7 ey
    have m1 : (if x < b.1 then x else b.1).toInt = min x.toInt b.1.toInt := by
      by_cases c : x < b.1
      · rw [ite_eq_left c]; have := Int32.lt_iff_toInt_lt.mp c; omega
      · rw [ite_eq_right c]; have := mt Int32.lt_iff_toInt_lt.mpr c; omega
    have m2 : (if y < b.2.1 then y else b.2.1).toInt = min y.toInt b.2.1.toInt := by
      by_cases c : y < b.2.1
      · rw [ite_eq_left c]; have := Int32.lt_iff_toInt_lt.mp c; omega
      · rw [ite_eq_right c]; have := mt Int32.lt_iff_toInt_lt.mpr c; omega
    have m3 : (if b.2.2 < y then y else b.2.2).toInt = max y.toInt b.2.2.toInt := by
      by_cases c : b.2.2 < y
      · rw [ite_eq_left c]; have := Int32.lt_iff_toInt_lt.mp c; omega
      · rw [ite_eq_right c]; have := mt Int32.lt_iff_toInt_lt.mpr c; omega
    rw [m1] at h1
    rw [m2] at h2
    rw [m3] at h3
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [ex, ey]; exact ⟨by omega, by omega, by omega⟩
      · exact h4 c hc
    · rcases h5 with h | ⟨c, hc, h⟩
      · split at h
        · exact Or.inr ⟨k, by simp, by rw [ex, h]⟩
        · exact Or.inl h
      · exact Or.inr ⟨c, by simp [hc], h⟩
    · rcases h6 with h | ⟨c, hc, h⟩
      · split at h
        · exact Or.inr ⟨k, by simp, by rw [ey, h]⟩
        · exact Or.inl h
      · exact Or.inr ⟨c, by simp [hc], h⟩
    · rcases h7 with h | ⟨c, hc, h⟩
      · split at h
        · exact Or.inr ⟨k, by simp, by rw [ey, h]⟩
        · exact Or.inl h
      · exact Or.inr ⟨c, by simp [hc], h⟩

theorem life105Bounds_facts (cells : Array UInt64) (hc : cells.size < 2 ^ 32) (h0 : cells.size ≠ 0)
    (B : Int32 × Int32 × Int32)
    (hB : life105Bounds cells 1 cells.size.toUInt32 (cellKeyX cells[0]!).toInt32 (cellKeyY cells[0]!).toInt32
      (cellKeyY cells[0]!).toInt32 = B) :
    (∀ c ∈ cells, B.1.toInt ≤ (keyCell c).1.toInt ∧ B.2.1.toInt ≤ (keyCell c).2.toInt ∧
        (keyCell c).2.toInt ≤ B.2.2.toInt) ∧
      (∃ c ∈ cells, (keyCell c).1 = B.1) ∧ (∃ c ∈ cells, (keyCell c).2 = B.2.1) ∧
      (∃ c ∈ cells, (keyCell c).2 = B.2.2) := by
  have hB' := life105Bounds_eq cells hc _ 1
    ((cellKeyX cells[0]!).toInt32, (cellKeyY cells[0]!).toInt32, (cellKeyY cells[0]!).toInt32) rfl
    (by rw [UInt32.toNat_one]; omega)
  rw [hB, UInt32.toNat_one] at hB'
  replace hB := hB'
  have hpos : 0 < cells.size := by omega
  have hl : cells.toList = cells[0] :: cells.toList.drop 1 := by
    simpa using toList_drop_eq_cons cells 0 hpos
  have hk : cells[0]! = cells[0] := getElem!_pos cells 0 hpos
  rw [hk] at hB
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := foldl_boundsStep (cells.toList.drop 1)
    ((cellKeyX cells[0]).toInt32, (cellKeyY cells[0]).toInt32, (cellKeyY cells[0]).toInt32)
  rw [← hB] at h1 h2 h3 h4 h5 h6 h7
  have hmem : ∀ c, c ∈ cells ↔ c = cells[0] ∨ c ∈ cells.toList.drop 1 := by
    intro c; rw [← Array.mem_toList_iff, hl]; simp
  have hm0 : cells[0] ∈ cells := Array.getElem_mem hpos
  refine ⟨fun c hc => ?_, ?_, ?_, ?_⟩
  · rcases (hmem c).mp hc with rfl | hc
    · exact ⟨h1, h2, h3⟩
    · exact h4 c hc
  · rcases h5 with h | ⟨c, hc, h⟩
    · exact ⟨cells[0], hm0, h.symm⟩
    · exact ⟨c, (hmem c).mpr (Or.inr hc), h⟩
  · rcases h6 with h | ⟨c, hc, h⟩
    · exact ⟨cells[0], hm0, h.symm⟩
    · exact ⟨c, (hmem c).mpr (Or.inr hc), h⟩
  · rcases h7 with h | ⟨c, hc, h⟩
    · exact ⟨cells[0], hm0, h.symm⟩
    · exact ⟨c, (hmem c).mpr (Or.inr hc), h⟩

/-- The cells left after a block, as a list. -/
theorem life105Rest_toList (cells : Array UInt64) (hc : cells.size < 2 ^ 31) (minX : Int32) :
    (U64Buf.toArray (life105Rest cells minX 0 cells.size.toUInt32 U64Buf.empty)).toList =
      cells.toList.filter (fun k => !inLife105Block minX k) := by
  rw [U64Buf.toArray_of_rep (life105Rest_spec cells hc minX _ 0 U64Buf.empty #[] rfl (by simp) U64Buf.rep_empty
    (by simp; omega))]
  simp

/--
The cells of the blocks inside their block are exactly the cells. `h` bounds the differences of the y coordinates.
-/
theorem mem_life105Split (h : Nat) :
    ∀ (n : Nat) (cells : Array UInt64), cells.size ≤ n → cells.size < 2 ^ 31 → 80 * (cells.size * h) < 2 ^ 31 →
      (∀ c ∈ cells, ∀ d ∈ cells, (keyCell c).2.toInt - (keyCell d).2.toInt < h) →
      ∀ q, (∃ b ∈ life105Split n cells, ∃ c ∈ b.1,
          (gridIndex b.2.1 b.2.2.1 80 (b.2.2.2 - b.2.2.1 + 1).toUInt32 (keyCell c)).isSome ∧ q = keyCell c) ↔
        ∃ c ∈ cells, q = keyCell c := by
  intro n
  induction n with
  | zero =>
    intro cells hn _ _ _ q
    have : cells.size = 0 := by omega
    simp only [life105Split, List.not_mem_nil, false_and, exists_false, false_iff, not_exists, not_and]
    intro c hc; have := Array.size_pos_of_mem hc; omega
  | succ n ih =>
    intro cells hn hc hh hy q
    by_cases h0 : cells.size = 0
    · simp only [life105Split, h0, ite_true, List.not_mem_nil, false_and, exists_false, false_iff, not_exists,
        not_and]
      intro c hc; have := Array.size_pos_of_mem hc; omega
    simp only [life105Split, h0, ite_false, List.mem_cons, exists_eq_or_imp]
    obtain ⟨hbox, ⟨cx, hcx, hcx'⟩, ⟨c1, hc1, hc1'⟩, ⟨c2, hc2, hc2'⟩⟩ := life105Bounds_facts cells (by omega) h0 _ rfl
    generalize life105Bounds cells 1 cells.size.toUInt32 (cellKeyX cells[0]!).toInt32 (cellKeyY cells[0]!).toInt32
      (cellKeyY cells[0]!).toInt32 = B at hbox hcx' hc1' hc2' ⊢
    have h80 : 80 * h < 2 ^ 31 := by
      have : 1 * h ≤ cells.size * h := Nat.mul_le_mul_right _ (by omega)
      omega
    have hspan : B.2.2.toInt - B.2.1.toInt < h := by rw [← hc1', ← hc2']; exact hy c2 hc2 c1 hc1
    -- A cell is inside the first block exactly when it is in its columns.
    have hin : ∀ c ∈ cells, (gridIndex B.1 B.2.1 80 (B.2.2 - B.2.1 + 1).toUInt32 (keyCell c)).isSome =
        inLife105Block B.1 c := by
      intro c hc
      obtain ⟨-, hy1, hy2⟩ := hbox c hc
      have hH := boxSize_toNat B.2.1 B.2.2 (by omega) (by omega)
      have hdy := boxOffset_toNat B.2.1 B.2.2 (keyCell c).2 hy1 hy2 (by omega)
      have hlt : ((keyCell c).2 - B.2.1).toUInt32 < (B.2.2 - B.2.1 + 1).toUInt32 := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold gridIndex inLife105Block
      by_cases hx : ((keyCell c).1 - B.1).toUInt32 < 80
      · rw [ite_eq_left ⟨hx, hlt⟩]; simp only [Option.isSome_some]; exact (decide_eq_true hx).symm
      · rw [ite_eq_right (fun h => hx h.1)]; simp only [Option.isSome_none]; exact (decide_eq_false hx).symm
    -- The rest.
    generalize hR : U64Buf.toArray (life105Rest cells B.1 0 cells.size.toUInt32 U64Buf.empty) = R
    have hRl : R.toList = cells.toList.filter (fun k => !inLife105Block B.1 k) := by
      rw [← hR]; exact life105Rest_toList cells hc B.1
    have hRmem : ∀ c, c ∈ R ↔ c ∈ cells ∧ inLife105Block B.1 c = false := by
      intro c; rw [← Array.mem_toList_iff, hRl, List.mem_filter, Array.mem_toList_iff]; simp
    have hRsz : R.size < cells.size := by
      have hcx_in : inLife105Block B.1 cx = true := by
        unfold inLife105Block; show decide (((keyCell cx).1 - B.1).toUInt32 < 80) = true
        rw [hcx', Int32.sub_self]; decide
      have : R.toList.length < cells.toList.length := by
        rw [hRl]
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨cx, Array.mem_toList_iff.mpr hcx, by simp [hcx_in]⟩
      simpa using this
    have ihR := ih R (by omega) (by omega) (by
        have : R.size * h ≤ cells.size * h := Nat.mul_le_mul_right _ (by omega)
        omega)
      (fun c hc d hd => hy c ((hRmem c).mp hc).1 d ((hRmem d).mp hd).1) q
    rw [ihR]
    constructor
    · rintro (⟨c, hc, -, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact ⟨c, hc, rfl⟩
      · exact ⟨c, ((hRmem c).mp hc).1, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      by_cases hb : inLife105Block B.1 c = true
      · exact Or.inl ⟨c, hc, by rw [hin c hc]; exact hb, rfl⟩
      · exact Or.inr ⟨c, (hRmem c).mpr ⟨hc, by simpa using hb⟩, rfl⟩

/-- Each block is at most `h` rows high, and the blocks have at most `n * (h + 1)` lines. -/
theorem life105Split_facts (h : Nat) :
    ∀ (n : Nat) (cells : Array UInt64), cells.size < 2 ^ 31 → 80 * (cells.size * h) < 2 ^ 31 →
      (∀ c ∈ cells, ∀ d ∈ cells, (keyCell c).2.toInt - (keyCell d).2.toInt < h) →
      (∀ b ∈ life105Split n cells, b.1.size < 2 ^ 32 ∧ 80 * b.height < 2 ^ 31) ∧
        ((life105Split n cells).flatMap Life105Block.lines).length ≤ n * (h + 1) := by
  intro n
  induction n with
  | zero => intro cells _ _ _; simp [life105Split]
  | succ n ih =>
    intro cells hc hh hy
    by_cases h0 : cells.size = 0
    · simp [life105Split, h0]
    simp only [life105Split, h0, ite_false, List.mem_cons, forall_eq_or_imp, List.flatMap_cons,
      List.length_append]
    obtain ⟨-, -, ⟨c1, hc1, hc1'⟩, ⟨c2, hc2, hc2'⟩⟩ := life105Bounds_facts cells (by omega) h0 _ rfl
    have hbox := (life105Bounds_facts cells (by omega) h0 _ rfl).1
    generalize life105Bounds cells 1 cells.size.toUInt32 (cellKeyX cells[0]!).toInt32 (cellKeyY cells[0]!).toInt32
      (cellKeyY cells[0]!).toInt32 = B at hbox hc1' hc2' ⊢
    have h80 : 80 * h < 2 ^ 31 := by
      have : 1 * h ≤ cells.size * h := Nat.mul_le_mul_right _ (by omega)
      omega
    have hspan : B.2.2.toInt - B.2.1.toInt < h := by rw [← hc1', ← hc2']; exact hy c2 hc2 c1 hc1
    have hle : B.2.1.toInt ≤ B.2.2.toInt := by have := hbox c1 hc1; omega
    have hH := boxSize_toNat B.2.1 B.2.2 hle (by omega)
    have hheight : Life105Block.height (cells, B.1, B.2.1, B.2.2) ≤ h := by
      unfold Life105Block.height; simp only; omega
    generalize hR : U64Buf.toArray (life105Rest cells B.1 0 cells.size.toUInt32 U64Buf.empty) = R
    have hRl : R.toList = cells.toList.filter (fun k => !inLife105Block B.1 k) := by
      rw [← hR]; exact life105Rest_toList cells hc B.1
    have hRmem : ∀ c ∈ R, c ∈ cells := by
      intro c hc'; rw [← Array.mem_toList_iff, hRl, List.mem_filter] at hc'; exact Array.mem_toList_iff.mp hc'.1
    have hRsz : R.size ≤ cells.size := by
      have := List.length_filter_le (fun k => !inLife105Block B.1 k) cells.toList
      rw [← hRl] at this; simpa using this
    obtain ⟨ihb, ihl⟩ := ih R (by omega) (by
        have : R.size * h ≤ cells.size * h := Nat.mul_le_mul_right _ hRsz
        omega) (fun c hc d hd => hy c (hRmem c hc) d (hRmem d hd))
    refine ⟨⟨⟨show cells.size < 2 ^ 32 by omega, by omega⟩, ihb⟩, ?_⟩
    rw [Life105Block.lines_length _ (by omega)]
    rw [Nat.succ_mul]
    omega

/-- Serialization is the header lines followed by the lines of the blocks. -/
theorem serializeLife105_eq (cells : Array UInt64) (hc : cells.size < 2 ^ 31)
    (hl : ((life105Split cells.size cells).flatMap Life105Block.lines).length + 2 < 2 ^ 31) :
    serializeLife105 cells =
      #["#Life 1.05", "#N"] ++ ((life105Split cells.size cells).flatMap Life105Block.lines).toArray := by
  have h1 := GrowBuf.rep_push (GrowBuf.rep_empty (α := String)) "#Life 1.05" (by decide)
  have h2 := GrowBuf.rep_push h1 "#N" (by decide)
  have := serializeLife105_loop_spec cells.size cells.size.toUInt32 cells #[] 0 _ _ (u32_size_toNat (by omega)) hc
    (by simp) (by simp) h2 (by simp only [Array.size_push, Array.size_empty]; omega)
  unfold serializeLife105
  rw [this.2.2.2]
  simp

/--
Round trip: deserializing serialized cells succeeds with no warnings and gives back exactly the cells. `h` bounds
the differences of the y coordinates of the cells.
-/
theorem life105_full_round_trip (cells : Array (Int32 × Int32)) (h : Nat) (hc : cells.size < 2 ^ 31)
    (hy : ∀ c ∈ cells, ∀ d ∈ cells, c.2.toInt - d.2.toInt < h)
    (hsz : 80 * (cells.size * (h + 1) + 2) < 2 ^ 31) :
    let r := deserializeLife105 (serializeLife105 (cells.map cellBits))
    r.status = .ok ∧ r.warnings = #[] ∧ ∀ q, cellBits q ∈ r.cells ↔ q ∈ cells := by
  intro r
  have hks : (cells.map cellBits).size = cells.size := by simp
  have hyk : ∀ c ∈ cells.map cellBits, ∀ d ∈ cells.map cellBits, (keyCell c).2.toInt - (keyCell d).2.toInt < h := by
    intro c hc d hd
    obtain ⟨c', hc', rfl⟩ := Array.mem_map.mp hc
    obtain ⟨d', hd', rfl⟩ := Array.mem_map.mp hd
    simpa using hy c' hc' d' hd'
  have hh : 80 * ((cells.map cellBits).size * h) < 2 ^ 31 := by
    rw [hks]; have : cells.size * h ≤ cells.size * (h + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨hbs, hlen⟩ := life105Split_facts h (cells.map cellBits).size (cells.map cellBits) (by omega) hh hyk
  have hlen' : 80 * (((life105Split (cells.map cellBits).size (cells.map cellBits)).flatMap
      Life105Block.lines).length + 2) < 2 ^ 31 := by rw [hks] at hlen ⊢; omega
  have hser := serializeLife105_eq (cells.map cellBits) (by omega) (by omega)
  obtain ⟨hst, hw, hmem⟩ := life105_round_trip _ hbs hlen'
  simp only [r, hser]
  refine ⟨hst, hw, fun q => ?_⟩
  rw [hmem q]
  have := mem_life105Split h _ (cells.map cellBits) (Nat.le_refl _) (by omega) hh hyk q
  refine Iff.trans this ?_
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c', hc', rfl⟩ := Array.mem_map.mp hc
    simpa using hc'
  · intro hq
    exact ⟨cellBits q, Array.mem_map_of_mem hq, by simp⟩

/-- A block is its `#P` line followed by rows of 80 `.` and `*` characters. -/
theorem serializeLife105Block_rows (cells : Array UInt64) (minX minY maxY : Int32) (hcs : cells.size < 2 ^ 32)
    (hwh : 80 * (maxY - minY + 1).toUInt32.toNat < 2 ^ 31) :
    ∀ l ∈ serializeLife105Block cells minX minY maxY,
      l = formatBlockHeader minX minY ∨ (l.toByteArray.size = 80 ∧ IsRow105 l.toByteArray) := by
  intro l hl
  rw [serializeLife105Block_eq cells minX minY maxY (by omega)] at hl
  simp only [Array.mem_append, List.mem_toArray, List.mem_map, List.mem_range] at hl
  rcases hl with hl | ⟨r, hr, rfl⟩
  · left; simpa using hl
  · right; exact life105_row_facts cells minX minY maxY hcs hwh r hr

/--
Every line of serialized cells is a header line, a `#P` block line or a row of 80 `.` and `*` characters.
-/
theorem serializeLife105_lines (cells : Array (Int32 × Int32)) (h : Nat) (hc : cells.size < 2 ^ 31)
    (hy : ∀ c ∈ cells, ∀ d ∈ cells, c.2.toInt - d.2.toInt < h)
    (hsz : 80 * (cells.size * (h + 1) + 2) < 2 ^ 31) :
    ∀ l ∈ serializeLife105 (cells.map cellBits), l = "#Life 1.05" ∨ l = "#N" ∨
      (∃ x y, l = formatBlockHeader x y) ∨ (l.toByteArray.size = 80 ∧ IsRow105 l.toByteArray) := by
  have hks : (cells.map cellBits).size = cells.size := by simp
  have hyk : ∀ c ∈ cells.map cellBits, ∀ d ∈ cells.map cellBits, (keyCell c).2.toInt - (keyCell d).2.toInt < h := by
    intro c hc d hd
    obtain ⟨c', hc', rfl⟩ := Array.mem_map.mp hc
    obtain ⟨d', hd', rfl⟩ := Array.mem_map.mp hd
    simpa using hy c' hc' d' hd'
  have hh : 80 * ((cells.map cellBits).size * h) < 2 ^ 31 := by
    rw [hks]; have : cells.size * h ≤ cells.size * (h + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨hbs, hlen⟩ := life105Split_facts h (cells.map cellBits).size (cells.map cellBits) (by omega) hh hyk
  rw [serializeLife105_eq (cells.map cellBits) (by omega) (by rw [hks] at hlen ⊢; omega)]
  intro l hl
  simp only [Array.mem_append, List.mem_toArray, List.mem_flatMap] at hl
  rcases hl with hl | ⟨b, hb, hl⟩
  · simp at hl; rcases hl with rfl | rfl <;> simp
  · right; right
    obtain ⟨h1, h2⟩ := hbs b hb
    unfold Life105Block.lines at hl
    rcases serializeLife105Block_rows b.1 b.2.1 b.2.2.1 b.2.2.2 h1 h2 l (Array.mem_toList_iff.mp hl) with he | he
    · exact Or.inl ⟨_, _, he⟩
    · exact Or.inr he

end Algorithm

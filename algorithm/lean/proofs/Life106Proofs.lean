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

import Algorithm.Life106

namespace Algorithm

theorem deserializeLife106_empty_Impl :
    deserializeLife106 #[] = ⟨1, 0, "", #[]⟩ := by
  unfold deserializeLife106
  rfl

theorem deserializeLife106_invalid_header_Impl (hdr : String) (h : hdr ≠ "#Life 1.06") :
    deserializeLife106 #[hdr] = ⟨2, 1, hdr, #[]⟩ := by
  unfold deserializeLife106
  have h_diff : (hdr != "#Life 1.06") = true := by
    rw [bne_iff_ne]
    exact h
  simp [h_diff]

theorem serializeLife106_empty_Impl :
    serializeLife106 #[] = #["#Life 1.06"] := by
  unfold serializeLife106
  unfold serializeLife106.loop
  rfl

theorem deserializeLife106_round_trip_empty_Impl :
    deserializeLife106 (serializeLife106 #[]) = ⟨0, 0, "", #[]⟩ := by
  unfold serializeLife106
  unfold serializeLife106.loop
  unfold deserializeLife106
  unfold deserializeLife106.loop
  rfl

theorem deserializeLife106_invalid_line_Impl (badLine : String) (h : parseCoordLine badLine = none) :
    deserializeLife106 #["#Life 1.06", badLine] = ⟨3, 2, badLine, #[]⟩ := by
  unfold deserializeLife106
  unfold deserializeLife106.loop
  simp [h]

/-- A single valid coordinate serialized in Life 1.06 produces header plus coordinate line. -/
theorem serializeLife106_single_Impl (c : Int32 × Int32) :
    serializeLife106 #[c] = #["#Life 1.06", s!"{c.1} {c.2}"] := by
  simp [serializeLife106, serializeLife106.loop]

/-- Two valid coordinates serialized in Life 1.06 produce header plus both coordinate lines in order. -/
theorem serializeLife106_double_Impl (c1 c2 : Int32 × Int32) :
    serializeLife106 #[c1, c2] = #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"] := by
  simp [serializeLife106, serializeLife106.loop]

/-- Deserializing a valid header with a single coordinate (10, 20) succeeds and recovers the coordinate. -/
theorem deserializeLife106_single_coord_Impl :
    deserializeLife106 #["#Life 1.06", "10 20"] = ⟨0, 0, "", #[(10, 20)]⟩ := by
  decide +kernel

/-- Round-trip theorem for the origin coordinate (0, 0). -/
theorem deserializeLife106_roundtrip_origin_Impl :
    deserializeLife106 (serializeLife106 #[(0, 0)]) = ⟨0, 0, "", #[(0, 0)]⟩ := by
  decide +kernel

/-- Round-trip theorem for non-trivial negative and positive coordinates. -/
theorem deserializeLife106_roundtrip_sample_Impl :
    deserializeLife106 (serializeLife106 #[(-5, 12), (42, -99)]) = ⟨0, 0, "", #[(-5, 12), (42, -99)]⟩ := by
  decide +kernel

/-- In the deserialization loop, the status is always either 0 (success) or 3 (invalid line). -/
theorem deserializeLife106_loop_status_cases (lines : Array String) (limit : UInt32) :
    ∀ (fuel : Nat) (i : UInt32) (acc : Array (Int32 × Int32)), limit.toNat - i.toNat ≤ fuel →
    (deserializeLife106.loop lines i limit acc).status = 0 ∨
    (deserializeLife106.loop lines i limit acc).status = 3 := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hfuel
    have h_not : ¬(i < limit) := by
      intro h
      have hlt := UInt32.lt_iff_toNat_lt.mp h
      omega
    unfold deserializeLife106.loop
    simp [h_not]
  | succ n ih =>
    intro i acc hfuel
    unfold deserializeLife106.loop
    by_cases h : i < limit
    · simp only [h, ↓reduceDIte]
      cases parseCoordLine lines[i.toNat]! with
      | none =>
        simp
      | some coord =>
        simp
        have h_dec : limit.toNat - (i + 1).toNat ≤ n := by
          have h1 := UInt32.lt_iff_toNat_lt.mp h
          have h2 : (i + 1).toNat = i.toNat + 1 := by
            rw [UInt32.toNat_add]
            have := UInt32.toNat_lt limit
            simp only [UInt32.toNat_one]
            omega
          omega
        exact ih (i + 1) (acc.push coord) h_dec
    · simp [h]

/-- For all input line sequences, deserialization returns a status in {0, 1, 2, 3}. -/
theorem deserializeLife106_status_cases_Impl (lines : Array String) :
    (deserializeLife106 lines).status = 0 ∨
    (deserializeLife106 lines).status = 1 ∨
    (deserializeLife106 lines).status = 2 ∨
    (deserializeLife106 lines).status = 3 := by
  unfold deserializeLife106
  by_cases h_empty : lines.size.toUInt32 == 0
  · simp [h_empty]
  · simp only [h_empty, Bool.false_eq_true, ↓reduceIte]
    by_cases h_hdr : lines[0]! != "#Life 1.06"
    · simp [h_hdr]
    · simp only [h_hdr, Bool.false_eq_true, ↓reduceIte]
      have h_loop := deserializeLife106_loop_status_cases lines lines.size.toUInt32
        (lines.size.toUInt32.toNat - 1) 1 #[] (Nat.le_refl _)
      rcases h_loop with h0 | h3
      · exact Or.inl h0
      · exact Or.inr (Or.inr (Or.inr h3))

/-- The result status of deserializeLife106 is always bounded by 3 for any input. -/
theorem deserializeLife106_status_le_3_Impl (lines : Array String) :
    (deserializeLife106 lines).status ≤ 3 := by
  have h := deserializeLife106_status_cases_Impl lines
  rcases h with h0 | h1 | h2 | h3
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h3]; decide

/-- A Life 1.06 coordinate array whose string representations invert under parseCoordLine. -/
def ValidLife106Coords (cells : Array (Int32 × Int32)) : Prop :=
  cells.size + 1 < 2 ^ 32 ∧
  ∀ (j : Nat) (h : j < cells.size),
    parseCoordLine s!"{(cells[j]).1} {(cells[j]).2}" = some cells[j]

theorem u32_ofNat_toNat {n : Nat} (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem u32_toNat_add_one {a : UInt32} (h : a.toNat + 1 < 2 ^ 32) : (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add]
  have : (1 : UInt32).toNat = 1 := rfl
  rw [this]
  exact Nat.mod_eq_of_lt h

theorem array_getElem_eq_getElem! {α : Type} [Inhabited α] (xs : Array α) (i : Nat) (hi : i < xs.size) :
    xs[i] = xs[i]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

theorem array_ext_getElem! {α : Type} [Inhabited α] (xs ys : Array α)
    (h_sz : xs.size = ys.size)
    (h_elem : ∀ (i : Nat), i < xs.size → xs[i]! = ys[i]!) :
    xs = ys := by
  apply Array.ext h_sz
  intro i hi1 hi2
  rw [array_getElem_eq_getElem! xs i hi1, array_getElem_eq_getElem! ys i hi2]
  exact h_elem i hi1

theorem array_getElem!_push_self {α : Type} [Inhabited α] (acc : Array α) (x : α) :
    (acc.push x)[acc.size]! = x := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]

theorem array_getElem!_push_lt {α : Type} [Inhabited α] (acc : Array α) (x : α) (k : Nat) (hk : k < acc.size) :
    (acc.push x)[k]! = acc[k]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hk,
    Array.getElem?_eq_getElem hk]

theorem serializeLife106_loop_spec (cells : Array (Int32 × Int32)) (limit : UInt32)
    (h_lim : limit.toNat = cells.size) (h_sz : cells.size < 2 ^ 32) :
    ∀ (n : Nat) (i : UInt32) (acc : Array String),
      limit.toNat - i.toNat = n →
      i.toNat ≤ limit.toNat →
      let res := serializeLife106.loop cells i limit acc
      res.size = acc.size + (limit.toNat - i.toNat) ∧
      (∀ (k : Nat), k < acc.size → res[k]! = acc[k]!) ∧
      (∀ (k : Nat), i.toNat ≤ k → k < limit.toNat →
        res[acc.size + (k - i.toNat)]! = s!"{(cells[k]!).1} {(cells[k]!).2}") := by
  intro n
  induction n with
  | zero =>
    intro i acc hn hle
    have h_not : ¬(i < limit) := by
      intro h
      have hlt := UInt32.lt_iff_toNat_lt.mp h
      omega
    unfold serializeLife106.loop
    rw [dite_eq_right h_not]
    dsimp only
    refine ⟨by omega, fun k hk => rfl, fun k h1 h2 => by omega⟩
  | succ n ih =>
    intro i acc hn hle
    have h_lt : i < limit := by
      rw [UInt32.lt_iff_toNat_lt]
      omega
    unfold serializeLife106.loop
    rw [dite_eq_left h_lt]
    dsimp only
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      apply u32_toNat_add_one
      omega
    have hn' : limit.toNat - (i + 1).toNat = n := by omega
    have hle' : (i + 1).toNat ≤ limit.toNat := by omega
    let acc' := acc.push s!"{(cells[i.toNat]!).1} {(cells[i.toNat]!).2}"
    have h_ih := ih (i + 1) acc' hn' hle'
    rcases h_ih with ⟨hsz_ih, hacc_ih, hcell_ih⟩
    have h_acc'_sz : acc'.size = acc.size + 1 := Array.size_push _
    refine ⟨?_, ?_, ?_⟩
    · rw [hsz_ih, h_acc'_sz]
      omega
    · intro k hk
      have hk' : k < acc'.size := by
        rw [h_acc'_sz]
        omega
      rw [hacc_ih k hk']
      exact array_getElem!_push_lt acc _ k hk
    · intro k hk1 hk2
      by_cases heq : k = i.toNat
      · subst heq
        have h_k_lt : acc.size < acc'.size := by
          rw [h_acc'_sz]
          omega
        have h_eq_idx : acc.size + (i.toNat - i.toNat) = acc.size := by omega
        rw [h_eq_idx]
        rw [hacc_ih acc.size h_k_lt]
        exact array_getElem!_push_self acc _
      · have hk1' : (i + 1).toNat ≤ k := by omega
        have h_arith : acc.size + (k - i.toNat) = acc'.size + (k - (i + 1).toNat) := by
          rw [h_acc'_sz, hi1]
          omega
        rw [h_arith]
        exact hcell_ih k hk1' hk2

theorem serializeLife106_spec (cells : Array (Int32 × Int32)) (h_sz : cells.size < 2 ^ 32) :
    (serializeLife106 cells).size = cells.size + 1 ∧
    (serializeLife106 cells)[0]! = "#Life 1.06" ∧
    ∀ (j : Nat), j < cells.size → (serializeLife106 cells)[j + 1]! = s!"{(cells[j]!).1} {(cells[j]!).2}" := by
  have h_lim : (cells.size.toUInt32).toNat = cells.size := u32_ofNat_toNat h_sz
  have h0 : (0 : UInt32).toNat = 0 := rfl
  have hsz0 : #["#Life 1.06"].size = 1 := rfl
  have h_spec := serializeLife106_loop_spec cells cells.size.toUInt32 h_lim h_sz cells.size 0 #["#Life 1.06"]
    (by omega) (by omega)
  rcases h_spec with ⟨h_sz_lines, h_hdr, h_coords⟩
  unfold serializeLife106
  refine ⟨by omega, ?_, ?_⟩
  · have h_zero_lt : 0 < #["#Life 1.06"].size := by decide
    have := h_hdr 0 h_zero_lt
    exact this
  · intro j hj
    have hj1 : (0 : UInt32).toNat ≤ j := by omega
    have hj2 : j < (cells.size.toUInt32).toNat := by rw [h_lim]; exact hj
    have h_cell := h_coords j hj1 hj2
    have h_idx : #["#Life 1.06"].size + (j - (0 : UInt32).toNat) = j + 1 := by omega
    rw [h_idx] at h_cell
    exact h_cell

/-- When limit ≤ i, deserializeLife106.loop immediately terminates and returns acc with status 0. -/
theorem deserializeLife106_loop_base (lines : Array String) (i limit : UInt32) (acc : Array (Int32 × Int32))
    (h_ge : limit ≤ i) :
    deserializeLife106.loop lines i limit acc = ⟨0, 0, "", acc⟩ := by
  unfold deserializeLife106.loop
  have h_not : ¬(i < limit) := by
    intro hlt
    have h1 := UInt32.lt_iff_toNat_lt.mp hlt
    have h2 := UInt32.le_iff_toNat_le.mp h_ge
    omega
  simp [h_not]

/-- Single step of deserializeLife106.loop when the line parses successfully. -/
theorem deserializeLife106_loop_step (lines : Array String) (i limit : UInt32) (acc : Array (Int32 × Int32))
    (h_lt : i < limit) (coord : Int32 × Int32)
    (h_parse : parseCoordLine lines[i.toNat]! = some coord) :
    deserializeLife106.loop lines i limit acc =
    deserializeLife106.loop lines (i + 1) limit (acc.push coord) := by
  conv =>
    lhs
    unfold deserializeLife106.loop
  simp only [h_lt, ↓reduceDIte, h_parse]

/-- When limit ≤ i, serializeLife106.loop immediately terminates and returns acc. -/
theorem serializeLife106_loop_base (cells : Array (Int32 × Int32)) (i limit : UInt32) (acc : Array String)
    (h_ge : limit ≤ i) :
    serializeLife106.loop cells i limit acc = acc := by
  unfold serializeLife106.loop
  have h_not : ¬(i < limit) := by
    intro hlt
    have h1 := UInt32.lt_iff_toNat_lt.mp hlt
    have h2 := UInt32.le_iff_toNat_le.mp h_ge
    omega
  simp [h_not]

/-- Single step of serializeLife106.loop. -/
theorem serializeLife106_loop_step (cells : Array (Int32 × Int32)) (i limit : UInt32) (acc : Array String)
    (h_lt : i < limit) :
    serializeLife106.loop cells i limit acc =
    serializeLife106.loop cells (i + 1) limit (acc.push s!"{(cells[i.toNat]!).1} {(cells[i.toNat]!).2}") := by
  conv =>
    lhs
    unfold serializeLife106.loop
  simp only [h_lt, ↓reduceDIte]

theorem deserializeLife106_loop_spec (lines : Array String) (limit : UInt32)
    (cells : Array (Int32 × Int32))
    (h_lim : limit.toNat = cells.size + 1)
    (h_sz : cells.size + 1 < 2 ^ 32)
    (h_lines : ∀ (j : Nat), j < cells.size → lines[j + 1]! = s!"{(cells[j]!).1} {(cells[j]!).2}")
    (h_valid : ∀ (j : Nat) (h : j < cells.size), parseCoordLine s!"{(cells[j]).1} {(cells[j]).2}" = some cells[j]) :
    ∀ (n : Nat) (i : UInt32) (acc : Array (Int32 × Int32)),
      limit.toNat - i.toNat = n →
      1 ≤ i.toNat → i.toNat ≤ limit.toNat →
      acc.size = i.toNat - 1 →
      (∀ (k : Nat), k < acc.size → acc[k]! = cells[k]!) →
      deserializeLife106.loop lines i limit acc = ⟨0, 0, "", cells⟩ := by
  intro n
  induction n with
  | zero =>
    intro i acc hn h1 hle h_acc_sz h_acc_elem
    have h_not : ¬(i < limit) := by
      intro h
      have hlt := UInt32.lt_iff_toNat_lt.mp h
      omega
    unfold deserializeLife106.loop
    rw [dite_eq_right h_not]
    have h_eq : acc = cells := by
      apply array_ext_getElem!
      · omega
      · intro k hk
        exact h_acc_elem k hk
    rw [h_eq]
  | succ n ih =>
    intro i acc hn h1 hle h_acc_sz h_acc_elem
    have h_lt : i < limit := by
      rw [UInt32.lt_iff_toNat_lt]
      omega
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      apply u32_toNat_add_one
      omega
    let j := i.toNat - 1
    have hj_lt : j < cells.size := by omega
    have hj_idx : j + 1 = i.toNat := by omega
    have h_line : lines[i.toNat]! = s!"{(cells[j]).1} {(cells[j]).2}" := by
      have hl := h_lines j hj_lt
      rw [← hj_idx]
      have h_cell_j : cells[j]! = cells[j] := (array_getElem_eq_getElem! cells j hj_lt).symm
      rw [h_cell_j] at hl
      exact hl
    have h_parse : parseCoordLine lines[i.toNat]! = some cells[j] := by
      rw [h_line]
      exact h_valid j hj_lt
    rw [deserializeLife106_loop_step lines i limit acc h_lt (cells[j]) h_parse]
    have hn' : limit.toNat - (i + 1).toNat = n := by omega
    have h1' : 1 ≤ (i + 1).toNat := by omega
    have hle' : (i + 1).toNat ≤ limit.toNat := by omega
    let acc' := acc.push cells[j]
    have h_acc'_sz : acc'.size = (i + 1).toNat - 1 := by
      change (acc.push cells[j]).size = _
      rw [Array.size_push]
      omega
    have h_acc'_elem : ∀ (k : Nat), k < acc'.size → acc'[k]! = cells[k]! := by
      intro k hk
      have hk_lt : k < acc.size + 1 := by
        change k < (acc.push cells[j]).size at hk
        rw [Array.size_push] at hk
        exact hk
      by_cases h_last : k = acc.size
      · have hk_eq_j : acc.size = j := by omega
        rw [h_last]
        change (acc.push cells[j])[acc.size]! = _
        rw [array_getElem!_push_self]
        have h_cell_j : cells[j]! = cells[j] := (array_getElem_eq_getElem! cells j hj_lt).symm
        rw [hk_eq_j]
        exact h_cell_j.symm
      · have hk_acc : k < acc.size := by omega
        change (acc.push cells[j])[k]! = _
        rw [array_getElem!_push_lt acc _ k hk_acc]
        exact h_acc_elem k hk_acc
    exact ih (i + 1) acc' hn' h1' hle' h_acc'_sz h_acc'_elem

/-- Universal round-trip for any coordinate array whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_universal_Impl (cells : Array (Int32 × Int32))
    (h_valid : ValidLife106Coords cells) :
    deserializeLife106 (serializeLife106 cells) = ⟨0, 0, "", cells⟩ := by
  have h_sz : cells.size + 1 < 2 ^ 32 := h_valid.1
  have h_coords : ∀ (j : Nat) (h : j < cells.size), parseCoordLine s!"{(cells[j]).1} {(cells[j]).2}" = some cells[j] :=
    h_valid.2
  have h_sz_cells : cells.size < 2 ^ 32 := by omega
  have h_ser := serializeLife106_spec cells h_sz_cells
  rcases h_ser with ⟨h_sz_lines, h_hdr, h_lines⟩
  unfold deserializeLife106
  have h_lines_u32 : (serializeLife106 cells).size.toUInt32.toNat = cells.size + 1 := by
    rw [h_sz_lines]
    exact u32_ofNat_toNat h_sz
  have h_ne : (serializeLife106 cells).size.toUInt32 ≠ 0 := by
    intro h
    have h_nat := congrArg UInt32.toNat h
    have h0_nat : (0 : UInt32).toNat = 0 := rfl
    rw [h_lines_u32, h0_nat] at h_nat
    omega
  have h_lines_nz : ((serializeLife106 cells).size.toUInt32 == 0) = false := by
    cases hb : (serializeLife106 cells).size.toUInt32 == 0 with
    | false => rfl
    | true =>
      rw [beq_iff_eq] at hb
      exact False.elim (h_ne hb)
  rw [h_lines_nz]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  have h_hdr_eq : ((serializeLife106 cells)[0]! != "#Life 1.06") = false := by
    rw [h_hdr]
    decide
  rw [h_hdr_eq]
  have h1_nat : (1 : UInt32).toNat = 1 := rfl
  have h_empty_sz : (#[] : Array (Int32 × Int32)).size = 0 := rfl
  have h_loop := deserializeLife106_loop_spec (serializeLife106 cells) (serializeLife106 cells).size.toUInt32
    cells h_lines_u32 h_sz h_lines h_coords
    (cells.size) 1 #[]
    (by rw [h_lines_u32, h1_nat]; omega)
    (by rw [h1_nat]; omega)
    (by rw [h_lines_u32, h1_nat]; omega)
    (by rw [h1_nat]; rfl)
    (fun k hk => by rw [h_empty_sz] at hk; omega)
  exact h_loop

/-- Universal round-trip for any single coordinate whose string representation inverts under parseCoordLine. -/
theorem deserializeLife106_roundtrip_single_arbitrary_Impl (c : Int32 × Int32)
    (h_parse : parseCoordLine s!"{c.1} {c.2}" = some c) :
    deserializeLife106 (serializeLife106 #[c]) = ⟨0, 0, "", #[c]⟩ := by
  rw [serializeLife106_single_Impl]
  dsimp [deserializeLife106]
  have h_sz : #["#Life 1.06", s!"{c.1} {c.2}"].size.toUInt32 = 2 := rfl
  rw [h_sz]
  have h_step := deserializeLife106_loop_step #["#Life 1.06", s!"{c.1} {c.2}"] 1 2 #[] (by decide) c (by simp [h_parse])
  have h_base := deserializeLife106_loop_base #["#Life 1.06", s!"{c.1} {c.2}"] 2 2 #[c] (by decide)
  rw [h_step]
  exact h_base

/-- Universal round-trip for any two coordinates whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_double_arbitrary_Impl (c1 c2 : Int32 × Int32)
    (h_parse1 : parseCoordLine s!"{c1.1} {c1.2}" = some c1)
    (h_parse2 : parseCoordLine s!"{c2.1} {c2.2}" = some c2) :
    deserializeLife106 (serializeLife106 #[c1, c2]) = ⟨0, 0, "", #[c1, c2]⟩ := by
  rw [serializeLife106_double_Impl]
  dsimp [deserializeLife106]
  have h_sz : #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"].size.toUInt32 = 3 := rfl
  rw [h_sz]
  have h_step1 := deserializeLife106_loop_step #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"]
    1 3 #[] (by decide) c1 (by simp [h_parse1])
  have h_step2 := deserializeLife106_loop_step #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"]
    2 3 #[c1] (by decide) c2 (by simp [h_parse2])
  have h_base := deserializeLife106_loop_base #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"]
    3 3 #[c1, c2] (by decide)
  rw [h_step1]
  change deserializeLife106.loop #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"] 2 3 #[c1] = _
  rw [h_step2]
  change deserializeLife106.loop #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}"] 3 3 #[c1, c2] = _
  exact h_base

/-- Serializing 3 valid coordinates in Life 1.06 produces header plus all 3 coordinate lines in order. -/
theorem serializeLife106_triple_Impl (c1 c2 c3 : Int32 × Int32) :
    serializeLife106 #[c1, c2, c3] = #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"] := by
  simp [serializeLife106, serializeLife106.loop]

/-- Universal round-trip for any three coordinates whose string representations invert under parseCoordLine. -/
theorem deserializeLife106_roundtrip_triple_arbitrary_Impl (c1 c2 c3 : Int32 × Int32)
    (h_parse1 : parseCoordLine s!"{c1.1} {c1.2}" = some c1)
    (h_parse2 : parseCoordLine s!"{c2.1} {c2.2}" = some c2)
    (h_parse3 : parseCoordLine s!"{c3.1} {c3.2}" = some c3) :
    deserializeLife106 (serializeLife106 #[c1, c2, c3]) = ⟨0, 0, "", #[c1, c2, c3]⟩ := by
  rw [serializeLife106_triple_Impl]
  dsimp [deserializeLife106]
  have h_sz : #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"].size.toUInt32 = 4 := rfl
  rw [h_sz]
  have h_step1 := deserializeLife106_loop_step #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"]
    1 4 #[] (by decide) c1 (by simp [h_parse1])
  have h_step2 := deserializeLife106_loop_step #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"]
    2 4 #[c1] (by decide) c2 (by simp [h_parse2])
  have h_step3 := deserializeLife106_loop_step #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"]
    3 4 #[c1, c2] (by decide) c3 (by simp [h_parse3])
  have h_base := deserializeLife106_loop_base #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"]
    4 4 #[c1, c2, c3] (by decide)
  rw [h_step1]
  change deserializeLife106.loop #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"] 2 4 #[c1] = _
  rw [h_step2]
  change deserializeLife106.loop #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"] 3 4 #[c1, c2] = _
  rw [h_step3]
  change deserializeLife106.loop #["#Life 1.06", s!"{c1.1} {c1.2}", s!"{c2.1} {c2.2}", s!"{c3.1} {c3.2}"] 4 4 #[c1, c2, c3] = _
  exact h_base

end Algorithm

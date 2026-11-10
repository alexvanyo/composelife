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

import proofs.RLEProofs

namespace Algorithm

/-!
# RLE deserialization of any input

`deserializeRLE` is `rleSpec` over the lines: comment lines (`#`, with `#R x y` offsets), the header, and then
the characters of the pattern lines (`rleLineSpec`), which give runs until `!`. The cells are the decoded runs.
-/

/-- The characters of `bytes` from byte `p` until `limit`: each with its position, code point and the position after
it. -/
def tokensFrom (bytes : ByteArray) (limit p : UInt32) : List (UInt32 × UInt32 × UInt32) :=
  if _h : p < limit then
    (p, (decodeCharAt bytes p limit).1, (decodeCharAt bytes p limit).2) ::
      tokensFrom bytes limit (decodeCharAt bytes p limit).2
  else []
termination_by limit.toNat - p.toNat
decreasing_by have := decodeCharAt_next bytes p limit _h; omega

/-- The successful result for runs `rs`: their cells, with rows starting at `sx`. -/
def rleFinish (ws : Array RLEWarning) (rs : Array (UInt32 × UInt32)) (sx sy : Int32) : RLEResult :=
  ⟨.ok, ws, (decodeRuns sx rs.toList sx sy).toArray.map cellBits⟩

/--
Reads the characters `ts` of line `i` (0-based, with bytes `bytes`) from column `col`, with a pending `count` (if
`has`, starting at byte `cP` and column `cCol`), and the warnings and runs so far; `next` is the next line, if any.
The pattern either ends on this line (`.inl`), or the line ends and the warnings and runs carry on (`.inr`).
-/
def rleLineSpec (bytes : ByteArray) (limit i : UInt32) (next : Option String) (sx sy : Int32) :
    List (UInt32 × UInt32 × UInt32) → UInt32 → UInt64 → Bool → UInt32 → UInt32 → Array RLEWarning →
      Array (UInt32 × UInt32) → RLEResult ⊕ (Array RLEWarning × Array (UInt32 × UInt32))
  | [], _, _, _, _, _, ws, rs => .inr (ws, rs)
  | (p, cp, p') :: ts, col, count, has, cP, cCol, ws, rs =>
    if cp >= 48 && cp <= 57 then
      rleLineSpec bytes limit i next sx sy ts (col + 1)
        (if count > 4294967296 then count else count * 10 + (cp.toUInt64 - 48)) true
        (if has then cP else p) (if has then cCol else col) ws rs
    else if cp == 33 then
      let ws := if has then ws.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p')) else ws
      let ws := if p' < limit then ws.push (.charAfterEnd (i + 1) (col + 2) ((decodeCharAt bytes p' limit).1))
        else match next with
          | some l => ws.push (.unexpectedInput (i + 2) 1 l)
          | none => ws
      .inl (rleFinish ws (rs.push (0, 1)) sx sy)
    else if cp == 32 || cp == 9 || cp == 13 then
      rleLineSpec bytes limit i next sx sy ts (col + 1) count has cP cCol ws rs
    else if has && count > maxRunCount then
      .inl ⟨.unexpectedInput (asciiStringLossy bytes cP p) (i + 1) (cCol + 1), #[], #[]⟩
    else
      let n : UInt32 := if has then count.toUInt32 else 1
      let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
      let ws := if tag == 2 && cp != 111 then ws.push (.unexpectedChar (i + 1) (col + 1) cp) else ws
      rleLineSpec bytes limit i next sx sy ts (col + 1) 0 false 0 0 ws (rs.push (tag, n))

/-- Reads the pattern lines `ls`, the first of which is line `i` (0-based). -/
def rleDataSpec (sx sy : Int32) : List String → UInt32 → Array RLEWarning → Array (UInt32 × UInt32) → RLEResult
  | [], _, ws, rs => rleFinish ws rs sx sy
  | l :: ls, i, ws, rs =>
    match rleLineSpec l.toByteArray l.toByteArray.size.toUInt32 i ls.head? sx sy
        (tokensFrom l.toByteArray l.toByteArray.size.toUInt32 0) 0 0 false 0 0 ws rs with
    | .inl r => r
    | .inr (ws, rs) => rleDataSpec sx sy ls (i + 1) ws rs

/-- Reads the comment lines `ls`, the first of which is line `i` (0-based), then the header and the pattern. -/
def rleCommentsSpec : List String → UInt32 → Int32 → Int32 → Bool → Array RLEWarning → RLEResult
  | [], _, _, _, _, ws => ⟨.invalidHeader "none", ws, #[]⟩
  | l :: ls, i, ox, oy, has, ws =>
    if l.toByteArray.size.toUInt32 != 0 && l.toByteArray.get! 0 == 35 then
      match parseRLEOffset l.toByteArray with
      | some c => rleCommentsSpec ls (i + 1) c.x c.y true
          (if has then ws.push (.duplicateOffset (i + 1) c.x c.y) else ws)
      | none => rleCommentsSpec ls (i + 1) ox oy has ws
    else if parseRLEHeader l.toByteArray == 3 then ⟨.ruleNotSupported, ws, #[]⟩
    else if parseRLEHeader l.toByteArray != 0 then ⟨.invalidHeader l, ws, #[]⟩
    else rleDataSpec ox oy ls (i + 1) ws #[]

/-- What `deserializeRLE` gives for any lines. -/
def rleSpec : List String → RLEResult
  | [] => ⟨.emptyFile, #[.emptyFile], #[]⟩
  | ls => rleCommentsSpec ls 0 0 0 false #[]

theorem tokensFrom_length_le (bytes : ByteArray) (limit : UInt32) :
    ∀ (n : Nat) (p : UInt32), limit.toNat - p.toNat ≤ n →
      (tokensFrom bytes limit p).length ≤ limit.toNat - p.toNat := by
  intro n
  induction n with
  | zero =>
    intro p hn
    rw [tokensFrom]
    have : ¬ p < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    simp [this]
  | succ n ih =>
    intro p hn
    rw [tokensFrom]
    by_cases h : p < limit
    · simp only [h, ↓reduceDIte, List.length_cons]
      have := decodeCharAt_next bytes p limit h
      have := ih (decodeCharAt bytes p limit).2 (by omega)
      omega
    · simp [h]

/-- `finishRLE` is `rleFinish`, for fewer than 2 ^ 31 cells. -/
theorem finishRLE_eq (warns : GrowBuf RLEWarning) (w : Array RLEWarning) (runs : GrowBuf (UInt32 × UInt32))
    (rs : Array (UInt32 × UInt32)) (sx sy : Int32) (hw : warns.Rep w) (hr : runs.Rep rs)
    (hrs : rs.size < 2 ^ 32) (hc : (decodeRuns sx rs.toList sx sy).length < 2 ^ 31) :
    finishRLE warns runs sx sy = rleFinish w rs sx sy := by
  unfold finishRLE rleFinish
  rw [hw.2.2.2, hr.2.2.2]
  have := expandRuns_spec rs hrs sx _ 0 sx sy U64Buf.empty #[] rfl (by simp) (by simpa using U64Buf.rep_empty)
    (by simpa using hc)
  simp only [show (0 : Nat).toUInt32 = 0 from rfl, List.drop_zero, Array.empty_append] at this
  simp only []
  rw [U64Buf.toArray_of_rep this]

theorem parseRLEData_line_spec (lines : Array String) (i : UInt32) (hi : i < lines.size.toUInt32)
    (next : Option String) (hnext : next = if i + 1 < lines.size.toUInt32 then some lines[(i + 1).toNat]! else none)
    (bytes : ByteArray) (limit : UInt32) (sx sy : Int32) :
    ∀ (n : Nat) (p col : UInt32) (count : UInt64) (has : Bool) (cP cCol : UInt32)
      (warns : GrowBuf RLEWarning) (w : Array RLEWarning) (runs : GrowBuf (UInt32 × UInt32))
      (rs : Array (UInt32 × UInt32)),
      limit.toNat - p.toNat ≤ n → warns.Rep w → runs.Rep rs →
      w.size + (limit.toNat - p.toNat) + 2 < 2 ^ 31 → rs.size + (limit.toNat - p.toNat) + 1 < 2 ^ 31 →
      match rleLineSpec bytes limit i next sx sy (tokensFrom bytes limit p) col count has cP cCol w rs with
      | .inl r => r.cells.size < 2 ^ 31 →
          parseRLEData lines lines.size.toUInt32 i true bytes limit p col count has cP cCol warns runs sx sy = r
      | .inr (w', rs') => ∃ (warns' : GrowBuf RLEWarning) (runs' : GrowBuf (UInt32 × UInt32)),
          warns'.Rep w' ∧ runs'.Rep rs' ∧ w'.size ≤ w.size + (limit.toNat - p.toNat) ∧
          rs'.size ≤ rs.size + (limit.toNat - p.toNat) ∧
          parseRLEData lines lines.size.toUInt32 i true bytes limit p col count has cP cCol warns runs sx sy =
            parseRLEData lines lines.size.toUInt32 (i + 1) false bytes limit 0 0 0 false 0 0 warns' runs' sx sy := by
  intro n
  induction n with
  | zero =>
    intro p col count has cP cCol warns w runs rs hn hw hr _ _
    have hnot : ¬ p < limit := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [tokensFrom]
    simp only [hnot, ↓reduceDIte, rleLineSpec]
    refine ⟨warns, runs, hw, hr, by omega, by omega, ?_⟩
    rw [parseRLEData]; simp [hi, hnot]
  | succ n ih =>
    intro p col count has cP cCol warns w runs rs hn hw hr hws hrs
    by_cases hp' : ¬ p < limit
    · rw [tokensFrom]
      simp only [hp', ↓reduceDIte, rleLineSpec]
      refine ⟨warns, runs, hw, hr, by omega, by omega, ?_⟩
      rw [parseRLEData]; simp [hi, hp']
    have hp : p < limit := Decidable.of_not_not hp'
    have hnx := decodeCharAt_next bytes p limit hp
    have htok : tokensFrom bytes limit p =
        (p, (decodeCharAt bytes p limit).1, (decodeCharAt bytes p limit).2) ::
          tokensFrom bytes limit (decodeCharAt bytes p limit).2 := by
      rw [tokensFrom]; simp [hp]
    rw [htok, parseRLEData]
    simp only [hi, ↓reduceDIte, ite_true, hp]
    generalize hr' : decodeCharAt bytes p limit = r at hnx ⊢
    obtain ⟨cp, p'⟩ := r
    simp only at hnx ⊢
    simp only [rleLineSpec]
    -- A recursive step: the result for the rest of the line.
    have step : ∀ (col' : UInt32) (count' : UInt64) (has' : Bool) (cP' cCol' : UInt32)
        (warns' : GrowBuf RLEWarning) (w' : Array RLEWarning) (runs' : GrowBuf (UInt32 × UInt32))
        (rs' : Array (UInt32 × UInt32)), warns'.Rep w' → runs'.Rep rs' → w'.size ≤ w.size + 1 →
        rs'.size ≤ rs.size + 1 →
        match rleLineSpec bytes limit i next sx sy (tokensFrom bytes limit p') col' count' has' cP' cCol' w' rs' with
        | .inl r => r.cells.size < 2 ^ 31 →
            parseRLEData lines lines.size.toUInt32 i true bytes limit p' col' count' has' cP' cCol' warns' runs'
              sx sy = r
        | .inr (w'', rs'') => ∃ (warns'' : GrowBuf RLEWarning) (runs'' : GrowBuf (UInt32 × UInt32)),
            warns''.Rep w'' ∧ runs''.Rep rs'' ∧ w''.size ≤ w.size + (limit.toNat - p.toNat) ∧
            rs''.size ≤ rs.size + (limit.toNat - p.toNat) ∧
            parseRLEData lines lines.size.toUInt32 i true bytes limit p' col' count' has' cP' cCol' warns' runs' sx sy =
              parseRLEData lines lines.size.toUInt32 (i + 1) false bytes limit 0 0 0 false 0 0 warns'' runs''
                sx sy := by
      intro col' count' has' cP' cCol' warns' w' runs' rs' hw' hr' hws' hrs'
      have := ih p' col' count' has' cP' cCol' warns' w' runs' rs' (by omega) hw' hr' (by omega) (by omega)
      revert this
      cases rleLineSpec bytes limit i next sx sy (tokensFrom bytes limit p') col' count' has' cP' cCol' w' rs' with
      | inl r => exact id
      | inr x =>
        obtain ⟨w'', rs''⟩ := x
        rintro ⟨a, b, c, d, e, f, g⟩
        exact ⟨a, b, c, d, by omega, by omega, g⟩
    by_cases hd : (cp ≥ 48 && cp ≤ 57) = true
    · simp only [hd, ite_true]
      exact step _ _ _ _ _ warns w runs rs hw hr (by omega) (by omega)
    simp only [hd, Bool.false_eq_true, ite_false]
    by_cases h33 : (cp == 33) = true
    · simp only [h33, ite_true]
      intro hcells
      have hw1 := GrowBuf.rep_push hw (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p')) (by omega)
      have hw1' : (if has then warns.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p'))
          else warns).Rep (if has then w.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p'))
          else w) := by cases has <;> simp [hw, hw1]
      have hs1 : (if has then w.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p'))
          else w).size ≤ w.size + 1 := by cases has <;> simp
      generalize (if has then warns.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p'))
          else warns) = W1 at hw1'
      generalize (if has then w.push (.unexpectedInput (i + 1) (cCol + 1) (asciiStringLossy bytes cP p'))
          else w) = w1 at hw1' hs1 hcells ⊢
      have hrp := GrowBuf.rep_push hr ((0 : UInt32), (1 : UInt32)) (by omega)
      subst hnext
      by_cases hp' : p' < limit
      · simp only [hp', ite_true] at hcells ⊢
        exact finishRLE_eq _ _ _ _ sx sy (GrowBuf.rep_push hw1' _ (by omega)) hrp (by simp; omega)
          (by simpa [rleFinish] using hcells)
      · simp only [hp', ite_false] at hcells ⊢
        by_cases hn1 : i + 1 < lines.size.toUInt32
        · simp only [hn1, ite_true] at hcells ⊢
          exact finishRLE_eq _ _ _ _ sx sy (GrowBuf.rep_push hw1' _ (by omega)) hrp (by simp; omega)
            (by simpa [rleFinish] using hcells)
        · simp only [hn1, ite_false] at hcells ⊢
          exact finishRLE_eq _ _ _ _ sx sy hw1' hrp (by simp; omega) (by simpa [rleFinish] using hcells)
    simp only [h33, Bool.false_eq_true, ite_false]
    by_cases hsp : (cp == 32 || cp == 9 || cp == 13) = true
    · simp only [hsp, ite_true]
      exact step _ _ _ _ _ warns w runs rs hw hr (by omega) (by omega)
    simp only [hsp, Bool.false_eq_true, ite_false]
    by_cases hbig : (has && count > maxRunCount) = true
    · simp only [hbig, ite_true]
      intro _
      simp
    simp only [hbig, Bool.false_eq_true, ite_false]
    generalize (if has then count.toUInt32 else 1) = nn
    generalize (if cp == 36 then (0 : UInt32) else if cp == 98 then 1 else 2) = tag
    have hrp := GrowBuf.rep_push hr (tag, nn) (by omega)
    by_cases hwarn : (tag == 2 && cp != 111) = true
    · simp only [hwarn, ite_true]
      exact step _ _ _ _ _ _ _ _ _ (GrowBuf.rep_push hw _ (by omega)) hrp (by simp) (by simp)
    · simp only [hwarn, Bool.false_eq_true, ite_false]
      exact step _ _ _ _ _ _ _ _ _ hw hrp (by simp) (by simp)

theorem drop_head?_eq (lines : Array String) (i : UInt32) (hs : lines.size < 2 ^ 32) (hi : i.toNat < lines.size) :
    (lines.toList.drop (i.toNat + 1)).head? =
      if i + 1 < lines.size.toUInt32 then some lines[(i + 1).toNat]! else none := by
  have hsucc := u32_toNat_succ hi hs
  rw [List.head?_drop]
  by_cases h : i.toNat + 1 < lines.size
  · have : i + 1 < lines.size.toUInt32 := by rw [u32_lt_size_iff hs, hsucc]; exact h
    simp only [this, ite_true]
    rw [hsucc, getElem!_pos lines (i.toNat + 1) h]
    simp [h]
  · have : ¬ i + 1 < lines.size.toUInt32 := by rw [u32_lt_size_iff hs, hsucc]; exact h
    simp only [this, ite_false]
    simp; omega

theorem parseRLEData_lines_spec (lines : Array String) (hls : lines.size < 2 ^ 31) (sx sy : Int32) :
    ∀ (n : Nat) (i : UInt32) (B : ByteArray) (L : UInt32) (warns : GrowBuf RLEWarning) (w : Array RLEWarning)
      (runs : GrowBuf (UInt32 × UInt32)) (rs : Array (UInt32 × UInt32)),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → warns.Rep w → runs.Rep rs →
      w.size + remBytes (lines.toList.drop i.toNat) + 2 < 2 ^ 31 →
      rs.size + remBytes (lines.toList.drop i.toNat) + 1 < 2 ^ 31 →
      (rleDataSpec sx sy (lines.toList.drop i.toNat) i w rs).cells.size < 2 ^ 31 →
      parseRLEData lines lines.size.toUInt32 i false B L 0 0 0 false 0 0 warns runs sx sy =
        rleDataSpec sx sy (lines.toList.drop i.toNat) i w rs := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i B L warns w runs rs hn hi hw hr _ hrs hc
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; omega
    have hdrop : lines.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hdrop] at hc ⊢
    rw [parseRLEData]
    simp only [hnot, ↓reduceDIte, rleDataSpec]
    exact finishRLE_eq warns w runs rs sx sy hw hr (by omega) (by simpa [rleDataSpec, rleFinish] using hc)
  | succ n ih =>
    intro i B L warns w runs rs hn hi hw hr hws hrs hc
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; exact hlt
    have hsucc := u32_toNat_succ hlt hs32
    have hnext := drop_head?_eq lines i hs32 hlt
    have hdrop := toList_drop_eq_cons lines i.toNat hlt
    rw [hdrop, remBytes_cons] at hws hrs
    rw [hdrop] at hc ⊢
    rw [parseRLEData]
    simp only [hyes, ↓reduceDIte, Bool.false_eq_true, ite_false, getElem!_pos lines i.toNat hlt]
    generalize hline : lines[i.toNat] = l at hws hrs hc ⊢
    generalize hrest : lines.toList.drop (i.toNat + 1) = rest at hws hrs hc hnext ⊢
    have hrest' : lines.toList.drop (i + 1).toNat = rest := by rw [hsucc, hrest]
    have hlsz : l.toByteArray.size.toUInt32.toNat - (0 : UInt32).toNat = l.toByteArray.size := by
      rw [UInt32.toNat_zero, Nat.sub_zero, u32_size_toNat (by omega)]
    have hL := parseRLEData_line_spec lines i hyes rest.head? hnext l.toByteArray l.toByteArray.size.toUInt32 sx sy
      _ 0 0 0 false 0 0 warns w runs rs (Nat.le_refl _) hw hr (by rw [hlsz]; omega) (by rw [hlsz]; omega)
    simp only [rleDataSpec] at hc ⊢
    revert hL hc
    cases rleLineSpec l.toByteArray l.toByteArray.size.toUInt32 i rest.head? sx sy
        (tokensFrom l.toByteArray l.toByteArray.size.toUInt32 0) 0 0 false 0 0 w rs with
    | inl r => intro hc hL; exact hL hc
    | inr x =>
      obtain ⟨w', rs'⟩ := x
      rintro hc ⟨warns', runs', hw', hr', hs1, hs2, heq⟩
      rw [hlsz] at hs1 hs2
      rw [heq]
      have := ih (i + 1) l.toByteArray l.toByteArray.size.toUInt32 warns' w' runs' rs' (by omega) (by omega) hw' hr'
        (by rw [hrest']; omega) (by rw [hrest']; omega) (by rw [hrest']; exact hc)
      rw [hrest'] at this
      exact this

theorem parseRLEComments_spec (lines : Array String) (hls : lines.size < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (ox oy : Int32) (has : Bool) (warns : GrowBuf RLEWarning) (w : Array RLEWarning),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → warns.Rep w →
      w.size + remBytes (lines.toList.drop i.toNat) + 2 < 2 ^ 31 →
      remBytes (lines.toList.drop i.toNat) + 1 < 2 ^ 31 →
      (rleCommentsSpec (lines.toList.drop i.toNat) i ox oy has w).cells.size < 2 ^ 31 →
      parseRLEComments lines lines.size.toUInt32 i ox oy has warns =
        rleCommentsSpec (lines.toList.drop i.toNat) i ox oy has w := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i ox oy has warns w hn hi hw _ _ _
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; omega
    rw [List.drop_eq_nil_of_le (by simp; omega), parseRLEComments]
    simp [hnot, rleCommentsSpec, hw.2.2.2]
  | succ n ih =>
    intro i ox oy has warns w hn hi hw hws hb hc
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hs32]; exact hlt
    have hsucc := u32_toNat_succ hlt hs32
    have hdrop := toList_drop_eq_cons lines i.toNat hlt
    rw [hdrop, remBytes_cons] at hws hb
    rw [hdrop] at hc ⊢
    rw [parseRLEComments]
    simp only [hyes, ↓reduceDIte, getElem!_pos lines i.toNat hlt, rleCommentsSpec] at hc ⊢
    generalize hline : lines[i.toNat] = l at hws hb hc ⊢
    generalize hrest : lines.toList.drop (i.toNat + 1) = rest at hws hb hc ⊢
    have hrest' : lines.toList.drop (i + 1).toNat = rest := by rw [hsucc, hrest]
    by_cases hC : (l.toByteArray.size.toUInt32 != 0 && l.toByteArray.get! 0 == 35) = true
    · simp only [hC, ite_true] at hc ⊢
      cases hpo : parseRLEOffset l.toByteArray with
      | some c =>
        simp only [hpo] at hc ⊢
        have hw' : (if has then warns.push (.duplicateOffset (i + 1) c.x c.y) else warns).Rep
            (if has then w.push (.duplicateOffset (i + 1) c.x c.y) else w) := by
          cases has <;> simp [hw, GrowBuf.rep_push hw _ (by omega)]
        have hs' : (if has then w.push (.duplicateOffset (i + 1) c.x c.y) else w).size ≤ w.size + 1 := by
          cases has <;> simp
        have := ih (i + 1) c.x c.y true _ _ (by omega) (by omega) hw' (by rw [hrest']; omega)
          (by rw [hrest']; omega) (by rw [hrest']; exact hc)
        rw [hrest'] at this
        exact this
      | none =>
        simp only [hpo] at hc ⊢
        have := ih (i + 1) ox oy has warns w (by omega) (by omega) hw (by rw [hrest']; omega)
          (by rw [hrest']; omega) (by rw [hrest']; exact hc)
        rw [hrest'] at this
        exact this
    · simp only [hC, Bool.false_eq_true, ite_false] at hc ⊢
      by_cases h3 : (parseRLEHeader l.toByteArray == 3) = true
      · simp [h3, hw.2.2.2]
      · simp only [h3, Bool.false_eq_true, ite_false] at hc ⊢
        by_cases h0 : (parseRLEHeader l.toByteArray != 0) = true
        · simp [h0, hw.2.2.2]
        · simp only [h0, Bool.false_eq_true, ite_false] at hc ⊢
          have := parseRLEData_lines_spec lines hls ox oy _ (i + 1) l.toByteArray 0 warns w GrowBuf.empty #[]
            rfl (by omega) hw GrowBuf.rep_empty (by rw [hrest']; omega) (by rw [hrest']; simp; omega)
            (by rw [hrest']; exact hc)
          rw [hrest'] at this
          exact this

/--
Deserialization of any lines (of fewer than 2 ^ 30 bytes in all) whose pattern has fewer than 2 ^ 31 alive cells is
`rleSpec`.
-/
theorem deserializeRLE_eq_spec (lines : Array String) (hls : lines.size < 2 ^ 31)
    (hb : remBytes lines.toList < 2 ^ 30) (hc : (rleSpec lines.toList).cells.size < 2 ^ 31) :
    deserializeRLE lines = rleSpec lines.toList := by
  have hs32 : lines.size < 2 ^ 32 := by omega
  unfold deserializeRLE
  by_cases h0 : lines.size = 0
  · have : lines.toList = [] := by simpa using h0
    simp [h0, this, rleSpec]
  have hne : (lines.size.toUInt32 == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg UInt32.toNat h; rw [u32_size_toNat hs32, UInt32.toNat_zero] at this; omega
  simp only [hne, Bool.false_eq_true, ite_false]
  have hl : lines.toList ≠ [] := by simpa using h0
  have hspec : rleSpec lines.toList = rleCommentsSpec lines.toList 0 0 0 false #[] := by
    unfold rleSpec; split
    · contradiction
    · rfl
  rw [hspec] at hc ⊢
  have := parseRLEComments_spec lines hls _ 0 0 0 false GrowBuf.empty #[] rfl (by simp) GrowBuf.rep_empty
    (by simp; omega) (by simp; omega) (by simpa using hc)
  simpa using this

end Algorithm

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
import proofs.SerialCoreProofs

namespace Algorithm

/-! ## Coordinate lines -/

theorem bytes_formatCoordLine (c : Int32 × Int32) :
    (formatCoordLine c.1.toUInt32 c.2.toUInt32).toByteArray.data.toList =
      (toString c.1).toByteArray.data.toList ++ 32 :: (toString c.2).toByteArray.data.toList := by
  show (toString c.1 ++ " " ++ toString c.2).toByteArray.data.toList = _
  rw [String.toByteArray_append, String.toByteArray_append, byteArray_append_toList, byteArray_append_toList]
  rw [List.append_assoc]
  rfl

theorem not_digit_32 : isDigitByte 32 = false := by decide
theorem space_32 : isSpaceByte 32 = true := by decide

/-- Every formatted coordinate line parses back to its coordinates. -/
theorem parseCoordLine_formatCoordLine (c : Int32 × Int32) :
    parseCoordLine (formatCoordLine c.1.toUInt32 c.2.toUInt32) = some c := by
  obtain ⟨x, y⟩ := c
  generalize hX : (toString x).toByteArray.data.toList = X
  generalize hY : (toString y).toByteArray.data.toList = Y
  have hL := bytes_formatCoordLine (x, y)
  simp only [hX, hY] at hL
  generalize hb : (formatCoordLine (x, y).1.toUInt32 (x, y).2.toUInt32).toByteArray = b at hL
  have hXlen : X.length ≤ 11 := hX ▸ bytes_toString_int32_length x
  have hYlen : Y.length ≤ 11 := hY ▸ bytes_toString_int32_length y
  have hsize : b.size = X.length + 1 + Y.length := by
    rw [byteArray_size_eq_length, hL]; simp; omega
  have hb32 : b.size < 2 ^ 32 := by omega
  have hXhead := hX ▸ bytes_toString_int32_head x
  have hYhead := hY ▸ bytes_toString_int32_head y
  have hXne : X ≠ [] := by
    rw [← hX, bytes_toString_int32]
    have := (natDigitBytes_spec x.toInt.natAbs).2.2
    split <;> simp_all
  have hYne : Y ≠ [] := by
    rw [← hY, bytes_toString_int32]
    have := (natDigitBytes_spec y.toInt.natAbs).2.2
    split <;> simp_all
  unfold parseCoordLine
  rw [hb]
  simp only
  -- The first number starts at 0.
  have hp0 : skipSpaces b 0 b.size.toUInt32 = 0 := by
    apply skipSpaces_of_not_space b hb32 0 (by simp)
    intro z hz
    rw [bytesFrom_eq_drop, hL] at hz
    simp only [UInt32.toNat_zero, List.drop_zero] at hz
    cases X with
    | nil => exact absurd rfl hXne
    | cons z' zs => simp at hz; subst hz; exact (hXhead z' (by simp)).1
  rw [hp0]
  have hX1 : parseInt32At b 0 b.size.toUInt32 = some ⟨x, X.length.toUInt32⟩ := by
    rw [parseInt32At_spec b hb32 0 (by simp), bytesFrom_eq_drop, hL]
    simp only [UInt32.toNat_zero, List.drop_zero]
    rw [← hX, parseInt32Spec_toString x (32 :: Y) (by intro z hz; simp at hz; subst hz; exact not_digit_32)]
    simp
  rw [hX1]
  simp only
  have he1 : X.length.toUInt32.toNat = X.length := u32_size_toNat (by omega)
  have hlt : X.length.toUInt32 < b.size.toUInt32 := by
    rw [u32_lt_size_iff hb32, he1]; omega
  have hget : b.get! X.length.toUInt32.toNat = 32 := by
    rw [he1, byteArray_get!_eq (by omega)]
    have : b.data.toList[X.length]'(by rw [← byteArray_size_eq_length]; omega) = 32 := by
      simp only [hL, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    rw [← this, Array.getElem_toList]
    rfl
  simp only [hlt, hget, space_32, decide_true, Bool.and_self, ite_true]
  -- The second number starts after the single space.
  have hp1 : skipSpaces b X.length.toUInt32 b.size.toUInt32 = (X.length + 1).toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [skipSpaces_spec b hb32 _ _ rfl (by omega), he1, u32_size_toNat (by omega), bytesFrom_eq_drop, hL,
      List.drop_left' rfl]
    cases Y with
    | nil => exact absurd rfl hYne
    | cons z zs =>
      have : ¬ isSpaceByte z = true := by simp [(hYhead z (by simp)).1]
      simp [List.takeWhile_cons_of_pos space_32, List.takeWhile_cons_of_neg this]
  rw [hp1]
  have he1' : (X.length + 1).toUInt32.toNat = X.length + 1 := u32_size_toNat (by omega)
  have hY1 : parseInt32At b (X.length + 1).toUInt32 b.size.toUInt32 =
      some ⟨y, (X.length + 1).toUInt32 + Y.length.toUInt32⟩ := by
    rw [parseInt32At_spec b hb32 _ (by omega), bytesFrom_eq_drop, hL, he1']
    have : List.drop (X.length + 1) (X ++ 32 :: Y) = (toString y).toByteArray.data.toList ++ [] := by
      rw [List.append_nil, hY, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left]
      rfl
    rw [this, parseInt32Spec_toString y [] (by simp), hY]
    simp
  rw [hY1]
  simp only
  have he2 : (X.length + 1).toUInt32 + Y.length.toUInt32 = b.size.toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, he1', u32_size_toNat (by omega), u32_size_toNat hb32]
    omega
  rw [he2, skipSpaces_of_not_space b hb32 _ (by rw [u32_size_toNat hb32]; exact Nat.le_refl _) (by
    intro z hz; rw [u32_size_toNat hb32, bytesFrom_of_ge (Nat.le_refl _)] at hz; simp at hz)]
  simp

/-! ## Deserialization -/

/-- What the deserialization loop computes from the remaining lines; `i` is the index of the next line. -/
def life106LoopSpec : List String → Nat → Array (Int32 × Int32) → Life106Result
  | [], _, a => ⟨0, 0, "", a⟩
  | l :: ls, i, a =>
    match parseCoordLine l with
    | some c => life106LoopSpec ls (i + 1) (a.push c)
    | none => ⟨3, (i + 1).toUInt32, l, #[]⟩

theorem array_toList_drop_of_lt {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) :
    xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h), Array.getElem_toList]

theorem deserializeLife106_loop_eq (lines : Array String) (hl : lines.size < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (acc : GrowBuf (Int32 × Int32)) (a : Array (Int32 × Int32)),
      lines.size - i.toNat = n → i.toNat ≤ lines.size → acc.Rep a → a.size + 1 = i.toNat →
      deserializeLife106.loop lines i lines.size.toUInt32 acc =
        life106LoopSpec (lines.toList.drop i.toNat) i.toNat a := by
  have hl32 : lines.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i acc a hn hi hrep ha
    have hnot : ¬ i < lines.size.toUInt32 := by rw [u32_lt_size_iff hl32]; omega
    rw [deserializeLife106.loop]
    simp only [hnot, ↓reduceDIte, List.drop_eq_nil_of_le (show lines.toList.length ≤ i.toNat by simp; omega),
      life106LoopSpec, hrep.2.2.2]
  | succ n ih =>
    intro i acc a hn hi hrep ha
    have hlt : i.toNat < lines.size := by omega
    have hyes : i < lines.size.toUInt32 := by rw [u32_lt_size_iff hl32]; exact hlt
    have hsucc := u32_toNat_succ hlt hl32
    rw [deserializeLife106.loop]
    simp only [hyes, ↓reduceDIte, array_toList_drop_of_lt lines i.toNat hlt, life106LoopSpec,
      getElem!_pos lines i.toNat hlt]
    cases hp : parseCoordLine lines[i.toNat] with
    | none =>
      simp only
      have : (i + 1) = (i.toNat + 1).toUInt32 := by
        apply UInt32.toNat_inj.mp
        rw [hsucc, u32_size_toNat (by omega)]
      rw [this]
    | some c =>
      simp only
      rw [ih (i + 1) (acc.push c) (a.push c) (by omega) (by omega) (GrowBuf.rep_push hrep c (by omega))
        (by simp; omega), hsucc]

/-- The deserialization loop either fails at the first line that doesn't parse or returns all coordinates. -/
theorem life106LoopSpec_eq (ls : List String) : ∀ (i : Nat) (a : Array (Int32 × Int32)),
    life106LoopSpec ls i a =
      match ls.mapM parseCoordLine with
      | some cs => ⟨0, 0, "", a ++ cs.toArray⟩
      | none =>
        let j := ls.findIdx (fun l => (parseCoordLine l).isNone)
        ⟨3, (i + j + 1).toUInt32, ls[j]!, #[]⟩ := by
  induction ls with
  | nil => intro i a; simp [life106LoopSpec]
  | cons l ls ih =>
    intro i a
    simp only [life106LoopSpec, List.mapM_cons, List.findIdx_cons]
    cases hp : parseCoordLine l with
    | none => simp
    | some c =>
      simp only [ih, Option.isNone_some, Bool.false_eq_true, ite_false]
      cases hm : ls.mapM parseCoordLine with
      | none =>
        simp only
        congr 1
        congr 1; omega
      | some cs => simp

theorem list_drop_one_getElem! {α : Type} [Inhabited α] (xs : Array α) (j : Nat) :
    (xs.toList.drop 1)[j]! = xs[j + 1]! := by
  simp [getElem!_def]

/-- Full specification of Life 1.06 deserialization. -/
theorem deserializeLife106_eq (lines : Array String) (hl : lines.size < 2 ^ 31) :
    deserializeLife106 lines =
      if lines.size = 0 then ⟨1, 0, "", #[]⟩
      else if lines[0]! ≠ "#Life 1.06" then ⟨2, 1, lines[0]!, #[]⟩
      else
        match (lines.toList.drop 1).mapM parseCoordLine with
        | some cells => ⟨0, 0, "", cells.toArray⟩
        | none =>
          let j := (lines.toList.drop 1).findIdx (fun l => (parseCoordLine l).isNone)
          ⟨3, (j + 2).toUInt32, lines[j + 1]!, #[]⟩ := by
  have hl32 : lines.size < 2 ^ 32 := by omega
  unfold deserializeLife106
  by_cases h0 : lines.size = 0
  · have : lines.size.toUInt32 = 0 := by rw [h0]; rfl
    simp [h0]
  · have : ¬ (lines.size.toUInt32 == 0) = true := by
      intro h; apply h0; have := congrArg UInt32.toNat (beq_iff_eq.mp h); rw [u32_size_toNat hl32] at this; exact this
    simp only [this, Bool.false_eq_true, ite_false, h0, bne_iff_ne, ne_eq]
    split
    · rfl
    · rw [deserializeLife106_loop_eq lines hl _ 1 GrowBuf.empty #[] rfl (by simp; omega) GrowBuf.rep_empty rfl,
        life106LoopSpec_eq]
      simp only [UInt32.toNat_one, Array.empty_append]
      cases (lines.toList.drop 1).mapM parseCoordLine with
      | some cs => rfl
      | none =>
        simp only [list_drop_one_getElem!]
        congr 2
        omega

/-! ## Serialization -/

theorem serializeLife106_loop_eq (cells : Array (UInt32 × UInt32)) (hc : cells.size + 2 < 2 ^ 31) :
    ∀ (n : Nat) (i : UInt32) (acc : GrowBuf String) (a : Array String),
      cells.size - i.toNat = n → i.toNat ≤ cells.size → acc.Rep a → a.size = i.toNat + 1 →
      (serializeLife106.loop cells i cells.size.toUInt32 acc).Rep
        (a ++ (cells.toList.drop i.toNat).toArray.map (fun c => formatCoordLine c.1 c.2)) := by
  have hc32 : cells.size < 2 ^ 32 := by omega
  intro n
  induction n with
  | zero =>
    intro i acc a hn hi hrep ha
    have hnot : ¬ i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc32]; omega
    rw [serializeLife106.loop]
    simp only [hnot, ↓reduceDIte, List.drop_eq_nil_of_le (show cells.toList.length ≤ i.toNat by simp; omega)]
    simpa using hrep
  | succ n ih =>
    intro i acc a hn hi hrep ha
    have hlt : i.toNat < cells.size := by omega
    have hyes : i < cells.size.toUInt32 := by rw [u32_lt_size_iff hc32]; exact hlt
    have hsucc := u32_toNat_succ hlt hc32
    rw [serializeLife106.loop]
    simp only [hyes, ↓reduceDIte, getElem!_pos cells i.toNat hlt]
    have := ih (i + 1) _ _ (by omega) (by omega)
      (GrowBuf.rep_push hrep (formatCoordLine cells[i.toNat].1 cells[i.toNat].2) (by omega)) (by simp; omega)
    rw [hsucc] at this
    rw [array_toList_drop_of_lt cells i.toNat hlt]
    simpa using this

/-- Full specification of Life 1.06 serialization. -/
theorem serializeLife106_eq (cells : Array (UInt32 × UInt32)) (hc : cells.size + 2 < 2 ^ 31) :
    serializeLife106 cells = #["#Life 1.06"] ++ cells.map (fun c => formatCoordLine c.1 c.2) := by
  have h1 := GrowBuf.rep_push (GrowBuf.rep_empty (α := String)) "#Life 1.06" (by decide)
  have := serializeLife106_loop_eq cells hc _ 0 _ _ rfl (by simp) h1 (by simp)
  unfold serializeLife106
  rw [this.2.2.2]
  simp

/-! ## Round trip -/

theorem mapM_parse_map_format (l : List (Int32 × Int32)) :
    (l.map (fun c => formatCoordLine c.1.toUInt32 c.2.toUInt32)).mapM parseCoordLine = some l := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [List.mapM_cons, parseCoordLine_formatCoordLine, ih]

/-- Deserializing serialized cells gives back exactly those cells, in order. -/
theorem deserializeLife106_serializeLife106 (cells : Array (Int32 × Int32)) (hc : cells.size + 2 < 2 ^ 31) :
    deserializeLife106 (serializeLife106 (cells.map cellBits)) = ⟨0, 0, "", cells⟩ := by
  rw [serializeLife106_eq _ (by simpa using hc), deserializeLife106_eq _ (by simp; omega)]
  have hmap : ((#["#Life 1.06"] ++ (cells.map cellBits).map (fun c => formatCoordLine c.1 c.2)).toList.drop 1).mapM
      parseCoordLine = some cells.toList := by
    simp only [Array.toList_append, Array.toList_map, List.singleton_append, List.drop_succ_cons,
      List.drop_zero, List.map_map]
    exact mapM_parse_map_format cells.toList
  have h0 : (#["#Life 1.06"] ++ (cells.map cellBits).map (fun c => formatCoordLine c.1 c.2))[0]! = "#Life 1.06" := by
    rw [getElem!_pos _ 0 (by simp; omega)]
    simp
  simp only [h0, hmap]
  simp

/-! ## Out-of-range coordinates -/

/-- A coordinate line whose first number, `sign ++ n`, doesn't fit in an `Int32` is rejected. -/
theorem parseCoordLine_first_out_of_range (neg : Bool) (n : Nat) (rest : String)
    (hn : if neg then 2 ^ 31 < n else 2 ^ 31 ≤ n)
    (hsz : ((if neg then "-" else "") ++ toString n ++ rest).toByteArray.size < 2 ^ 32)
    (hrest : ∀ y, rest.toByteArray.data.toList.head? = some y → isDigitByte y = false) :
    parseCoordLine ((if neg then "-" else "") ++ toString n ++ rest) = none := by
  have hd := natDigitBytes_digits n
  obtain ⟨hdr, hv, hne⟩ := natDigitBytes_spec n
  have htw := takeWhile_digits_append _ _ hd hrest
  generalize hb : ((if neg then "-" else "") ++ toString n ++ rest).toByteArray = b at hsz
  have hL : b.data.toList = (if neg then [45] else []) ++ (natDigitBytes n ++ rest.toByteArray.data.toList) := by
    rw [← hb, String.toByteArray_append, String.toByteArray_append, byteArray_append_toList,
      byteArray_append_toList, Nat.toString_eq_repr, bytes_natRepr, List.append_assoc]
    split <;> rfl
  obtain ⟨z, zs, hz⟩ : ∃ z zs, natDigitBytes n = z :: zs := by
    cases h : natDigitBytes n with
    | nil => exact absurd h hne
    | cons z zs => exact ⟨z, zs, rfl⟩
  have hzd : 48 ≤ z.toNat ∧ z.toNat ≤ 57 := hdr z (by rw [hz]; simp)
  unfold parseCoordLine
  rw [hb]
  simp only
  have hp0 : skipSpaces b 0 b.size.toUInt32 = 0 := by
    apply skipSpaces_of_not_space b hsz 0 (by simp)
    intro y hy
    rw [bytesFrom_eq_drop, hL, hz] at hy
    have h1 : z ≠ 32 := by intro h; subst h; simp at hzd
    have h2 : z ≠ 9 := by intro h; subst h; simp at hzd
    have h3 : z ≠ 13 := by intro h; subst h; simp at hzd
    split at hy <;> simp at hy <;> subst hy <;> simp_all [isSpaceByte] <;> decide
  rw [hp0, parseInt32At_spec b hsz 0 (by simp), bytesFrom_eq_drop, hL]
  simp only [UInt32.toNat_zero, List.drop_zero]
  unfold parseInt32Spec
  cases neg with
  | true =>
    simp only [ite_true, List.cons_append, List.nil_append, List.head?_cons, List.tail_cons, htw] at hn ⊢
    simp [hv, hn]
  | false =>
    have hz45 : z ≠ 45 := by intro h; subst h; simp at hzd
    simp only [Bool.false_eq_true, ite_false, List.nil_append] at hn ⊢
    rw [hz] at htw ⊢
    simp only [List.cons_append, List.head?_cons, Option.some.injEq, hz45, ite_false]
    rw [← List.cons_append, htw, ← hz, hv]
    simp [hn]

end Algorithm

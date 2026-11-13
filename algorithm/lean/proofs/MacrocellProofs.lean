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

import AlgorithmDefs
import proofs.SerialCoreProofs
import proofs.MacroCellQueryProofs

namespace Algorithm

/-! ## Well-formed nodes -/

/-- Every node in `data` is well formed, of depth at most 63. -/
def NodesOK (data : Array MacroCell) : Prop := ∀ e ∈ data, isWellFormed e ∧ e.depth ≤ 63

theorem wf_makeLevel4Node (a b c d : UInt64) :
    isWellFormed (makeLevel4Node a b c d) ∧ (makeLevel4Node a b c d).depth = 4 := by
  simp [makeLevel4Node, isWellFormed, MacroCell.depth]

theorem wf_makeCellNode (a b c d : MacroCell) (ha : isWellFormed a) (hb : isWellFormed b) (hc : isWellFormed c)
    (hd : isWellFormed d) (h1 : b.depth = a.depth) (h2 : c.depth = a.depth) (h3 : d.depth = a.depth) :
    isWellFormed (makeCellNode a b c d) ∧ (makeCellNode a b c d).depth = a.depth + 1 := by
  constructor
  · simp only [makeCellNode, isWellFormed]; exact ⟨ha, hb, hc, hd, h1.symm, by omega, by omega⟩
  · simp [makeCellNode, MacroCell.depth]

theorem level_toNat_eq_depth : ∀ (m : MacroCell), m.depth < 2 ^ 32 → m.level.toNat = m.depth
  | .level4Node .., _ => rfl
  | .cellNode _ nw _ _ _, h => by
    simp only [MacroCell.depth] at h
    simp only [MacroCell.level, MacroCell.depth]
    rw [UInt32.toNat_add, level_toNat_eq_depth nw (by omega)]
    simp; omega

theorem emptyMacroCellUInt32_loop_ok (level : UInt32) (hl : level.toNat ≤ 63) :
    ∀ (n : Nat) (cur : UInt32) (node : MacroCell), level.toNat - cur.toNat = n → 4 ≤ cur.toNat →
      cur.toNat ≤ level.toNat → isWellFormed node → node.depth = cur.toNat →
      isWellFormed (emptyMacroCellUInt32.loop level cur node) ∧
        (emptyMacroCellUInt32.loop level cur node).depth = level.toNat := by
  intro n
  induction n with
  | zero =>
    intro cur node hn h4 hle hwf hd
    have hnot : ¬ cur < level := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [emptyMacroCellUInt32.loop]
    simp only [hnot, ↓reduceDIte]
    exact ⟨hwf, by omega⟩
  | succ n ih =>
    intro cur node hn h4 hle hwf hd
    have hlt : cur < level := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (cur + 1).toNat = cur.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    rw [emptyMacroCellUInt32.loop]
    simp only [hlt, ↓reduceDIte]
    obtain ⟨hw, hdep⟩ := wf_makeCellNode node node node node hwf hwf hwf hwf rfl rfl rfl
    exact ih (cur + 1) _ (by omega) (by omega) (by omega) hw (by rw [hdep, hd, hsucc])

theorem emptyMacroCellUInt32_ok (level : UInt32) (h4 : 4 ≤ level.toNat) (hl : level.toNat ≤ 63) :
    isWellFormed (emptyMacroCellUInt32 level) ∧ (emptyMacroCellUInt32 level).depth = level.toNat :=
  emptyMacroCellUInt32_loop_ok level hl _ 4 emptyLevel4 rfl (by decide) h4
    (wf_makeLevel4Node 0 0 0 0).1 (wf_makeLevel4Node 0 0 0 0).2

theorem nodesOK_default (data : Array MacroCell) (h : NodesOK data) (i : Nat) :
    isWellFormed data[i]! ∧ data[i]!.depth ≤ 63 := by
  by_cases hi : i < data.size
  · rw [getElem!_pos data i hi]; exact h _ (Array.getElem_mem hi)
  · rw [getElem!_neg data i hi]
    show isWellFormed emptyLevel4 ∧ emptyLevel4.depth ≤ 63
    have := wf_makeLevel4Node 0 0 0 0
    exact ⟨this.1, by unfold emptyLevel4; omega⟩

/-- `macroCellAt` rebuilds a node to an equal-depth, still well formed node. -/
theorem macroCellAt_ok (data : Array MacroCell) (h : NodesOK data) (i : UInt32) :
    isWellFormed (macroCellAt data i) ∧ (macroCellAt data i).depth = data[i.toNat]!.depth := by
  have hok := nodesOK_default data h i.toNat
  unfold macroCellAt
  generalize data[i.toNat]! = m at hok ⊢
  cases m with
  | level4Node _ a b c d => exact ⟨(wf_makeLevel4Node a b c d).1, (wf_makeLevel4Node a b c d).2⟩
  | cellNode _ a b c d =>
    simp only [isWellFormed] at hok
    obtain ⟨⟨ha, hb, hc, hd, h1, h2, h3⟩, -⟩ := hok
    obtain ⟨hw, hdep⟩ := wf_makeCellNode a b c d ha hb hc hd h1.symm (by omega) (by omega)
    exact ⟨hw, by rw [hdep]; rfl⟩

theorem mem_copyPrefix [Inhabited α] (src : Array α) (n : UInt32) :
    ∀ (m : Nat) (i : UInt32) (dst : Array α), n.toNat - i.toNat = m →
      ∀ e ∈ copyPrefix src n i dst, e ∈ dst ∨ e ∈ src ∨ e = default := by
  intro m
  induction m with
  | zero =>
    intro i dst hm e he
    have hnot : ¬ i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    rw [copyPrefix] at he
    simp only [hnot, ↓reduceDIte] at he
    exact Or.inl he
  | succ m ih =>
    intro i dst hm e he
    have hlt : i < n := by rw [UInt32.lt_iff_toNat_lt]; omega
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt32.toNat_add]; have := UInt32.toNat_lt n; simp only [UInt32.toNat_one]; omega
    rw [copyPrefix] at he
    simp only [hlt, ↓reduceDIte] at he
    rcases ih (i + 1) _ (by omega) e he with h | h | h
    · simp only [Array.set!_eq_setIfInBounds] at h
      rcases Array.mem_or_eq_of_mem_setIfInBounds h with h' | rfl
      · exact Or.inl h'
      · by_cases hi : i.toNat < src.size
        · rw [getElem!_pos src _ hi]; exact Or.inr (Or.inl (Array.getElem_mem hi))
        · rw [getElem!_neg src _ hi]; exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem nodesOK_push (b : GrowBuf MacroCell) (h : NodesOK b.data) (x : MacroCell) (hx : isWellFormed x ∧ x.depth ≤ 63) :
    NodesOK (b.push x).data := by
  intro e he
  unfold GrowBuf.push at he
  split at he
  · simp only [Array.set!_eq_setIfInBounds] at he
    rcases Array.mem_or_eq_of_mem_setIfInBounds he with h' | rfl
    · exact h e h'
    · exact hx
  · dsimp only at he
    letI : Inhabited MacroCell := ⟨x⟩
    rcases mem_copyPrefix b.data b.data.size.toUInt32 _ 0 _ rfl e he with h' | h' | h'
    · rw [Array.mem_replicate] at h'; rw [h'.2]; exact hx
    · exact h e h'
    · rw [h']; exact hx

theorem cellChild_ok (nodes : GrowBuf MacroCell) (isLeaf : GrowBuf Bool) (h : NodesOK nodes.data) (L : UInt32)
    (h5 : 5 ≤ L.toNat) (h63 : L.toNat ≤ 63) (id : UInt32) (c : MacroCell)
    (hc : macrocellCellChild nodes isLeaf L (emptyMacroCellUInt32 (L - 1)) id = some c) :
    isWellFormed c ∧ c.depth = L.toNat - 1 := by
  have hL1 : (L - 1).toNat = L.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp
  unfold macrocellCellChild at hc
  split at hc
  · simp only [Option.some.injEq] at hc
    subst hc
    have := emptyMacroCellUInt32_ok (L - 1) (by omega) (by omega)
    exact ⟨this.1, by rw [this.2, hL1]⟩
  · split at hc
    · simp at hc
    · split at hc
      · simp at hc
      · dsimp only at hc
        split at hc
        · rename_i hlev
          simp only [Option.some.injEq] at hc
          subst hc
          obtain ⟨hw, hd⟩ := macroCellAt_ok nodes.data h (id - 1)
          have hb := (nodesOK_default nodes.data h (id - 1).toNat).2
          refine ⟨hw, ?_⟩
          have hlevel := level_toNat_eq_depth (macroCellAt nodes.data (id - 1)) (by omega)
          have := congrArg UInt32.toNat (beq_iff_eq.mp hlev)
          rw [UInt32.toNat_add, hlevel] at this
          simp at this
          omega
        · simp at hc

/-- The deserialization loop returns a well-formed node of depth at most 63. -/
theorem deserializeMacrocell_loop_ok (lines : Array String) (numLines : UInt32) (i : UInt32) (inLeaf : Bool)
    (bytes : ByteArray) (limit p col x y : UInt32) (leaf : UInt64) (nodes : GrowBuf MacroCell)
    (leaves : GrowBuf UInt64) (isLeaf : GrowBuf Bool) (warns : GrowBuf MacrocellWarning) :
    NodesOK nodes.data →
      isWellFormed (deserializeMacrocell.loop lines numLines i inLeaf bytes limit p col x y leaf nodes leaves isLeaf
        warns).macroCell ∧
      (deserializeMacrocell.loop lines numLines i inLeaf bytes limit p col x y leaf nodes leaves isLeaf
        warns).macroCell.depth ≤ 63 := by
  have hempty : isWellFormed emptyLevel4 ∧ emptyLevel4.depth ≤ 63 := by
    have := wf_makeLevel4Node 0 0 0 0
    exact ⟨this.1, by unfold emptyLevel4; omega⟩
  fun_induction deserializeMacrocell.loop lines numLines i inLeaf bytes limit p col x y leaf nodes leaves isLeaf warns
  all_goals intro hok
  all_goals first
    | exact hempty
    | (rename_i ih; exact ih hok)
    | (rename_i ih
       exact ih (nodesOK_push _ hok _ ⟨(wf_makeLevel4Node _ _ _ _).1, by rw [(wf_makeLevel4Node _ _ _ _).2]; omega⟩))
    | (obtain ⟨hw, hd⟩ := macroCellAt_ok _ hok (GrowBuf.size _ - 1)
       exact ⟨hw, by rw [hd]; exact (nodesOK_default _ hok _).2⟩)
    | skip
  case case17 =>
    rename_i n _ hbound h4 _ c1 hc1 c2 hc2 c3 hc3 c4 hc4 ih
    have h5 : 5 ≤ n.level.toNat ∧ n.level.toNat ≤ 63 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, maxMacrocellLevel] at hbound
      have h1 : ¬ n.level.toNat < 4 := fun h => hbound.1 (UInt32.lt_iff_toNat_lt.mpr h)
      have h2 : ¬ 63 < n.level.toNat := fun h =>
        hbound.2 (decide_eq_true ((UInt32.lt_iff_toNat_lt (a := (63 : UInt32)) (b := n.level)).mpr h))
      have h3 : n.level.toNat ≠ 4 := by
        intro h; apply h4; rw [beq_iff_eq]; apply UInt32.toNat_inj.mp; rw [h]; rfl
      simp at h1 h2
      omega
    obtain ⟨w1, d1⟩ := cellChild_ok _ _ hok n.level h5.1 h5.2 _ c1 hc1
    obtain ⟨w2, d2⟩ := cellChild_ok _ _ hok n.level h5.1 h5.2 _ c2 hc2
    obtain ⟨w3, d3⟩ := cellChild_ok _ _ hok n.level h5.1 h5.2 _ c3 hc3
    obtain ⟨w4, d4⟩ := cellChild_ok _ _ hok n.level h5.1 h5.2 _ c4 hc4
    obtain ⟨hw, hd⟩ := wf_makeCellNode c1 c2 c3 c4 w1 w2 w3 w4 (by omega) (by omega) (by omega)
    exact ih (nodesOK_push _ hok _ ⟨hw, by omega⟩)

/--
Deserialization always returns a well-formed node (the children of every node have equal depths) of depth at most
63, whatever the input.
-/
theorem deserializeMacrocell_wellFormed_Impl (lines : Array String) :
    isWellFormed (deserializeMacrocell lines).macroCell ∧ (deserializeMacrocell lines).macroCell.depth ≤ 63 := by
  have hempty : isWellFormed emptyLevel4 ∧ emptyLevel4.depth ≤ 63 := by
    have := wf_makeLevel4Node 0 0 0 0
    exact ⟨this.1, by unfold emptyLevel4; omega⟩
  unfold deserializeMacrocell
  dsimp only
  split
  · exact hempty
  · split
    · exact hempty
    · apply deserializeMacrocell_loop_ok
      intro e he
      simp [GrowBuf.empty] at he

/-! ## Node lines -/

theorem drop_sep {R : List UInt8} (D : List UInt8) (L : List UInt8) (k : Nat) (h : L.drop k = 32 :: (D ++ R)) :
    L.drop (k + 1 + D.length) = R := by
  rw [show k + 1 + D.length = k + (1 + D.length) by omega, ← List.drop_drop, h, Nat.add_comm, List.drop_succ_cons,
    List.drop_left' rfl]

/-- Skipping `m` spaces and then parsing a number. -/
theorem skipParse_list (L : List UInt8) (hL : L.length < 2 ^ 32) (p : UInt32) (v m : Nat) (hp : p.toNat = v)
    (n : UInt32) (rest : List UInt8) (hsplit : L.drop v = List.replicate m 32 ++ (natDigitBytes n.toNat ++ rest))
    (hrest : ∀ y, rest.head? = some y → isDigitByte y = false) :
    skipSpaces ⟨L.toArray⟩ p (⟨L.toArray⟩ : ByteArray).size.toUInt32 = (v + m).toUInt32 ∧
      parseUInt32At ⟨L.toArray⟩ (v + m).toUInt32 (⟨L.toArray⟩ : ByteArray).size.toUInt32 =
        some ⟨n, (v + m + (natDigitBytes n.toNat).length).toUInt32⟩ := by
  have hlen := congrArg List.length hsplit
  simp only [List.length_drop, List.length_append, List.length_replicate] at hlen
  have hsz : (⟨L.toArray⟩ : ByteArray).size < 2 ^ 32 := by rw [size_of_list]; exact hL
  obtain ⟨hd, -, hne⟩ := natDigitBytes_spec n.toNat
  have hfirst : ∀ y, (natDigitBytes n.toNat ++ rest).head? = some y → isSpaceByte y = false := by
    intro y hy
    cases hD : natDigitBytes n.toNat with
    | nil => exact absurd hD hne
    | cons z zs =>
      rw [hD] at hy; simp at hy; subst hy
      exact isDigitByte_not_space ((isDigitByte_iff _).mpr (hd _ (by rw [hD]; simp)))
  have hv : v ≤ L.length := by
    by_cases h : v ≤ L.length
    · exact h
    · rw [List.drop_eq_nil_of_le (by omega)] at hsplit
      cases hD : natDigitBytes n.toNat with
      | nil => exact absurd hD hne
      | cons _ _ => rw [hD] at hsplit; simp at hsplit
  refine ⟨skipSpaces_list L hL p v m hp hv _ hsplit hfirst, ?_⟩
  rw [parseUInt32At_digits _ hsz _ n rest (by
    rw [bytesFrom_of_list, u32_size_toNat (by omega), ← List.drop_drop, hsplit, List.drop_left']; simp) hrest]
  simp only [Option.some.injEq]
  congr 1
  apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, u32_size_toNat (by omega), u32_size_toNat (by omega),
    u32_size_toNat (by omega)]; omega

theorem bytes_formatMacrocellNode (level nw ne sw se : UInt32) :
    (formatMacrocellNode level nw ne sw se).toByteArray.data.toList =
      natDigitBytes level.toNat ++ 32 :: (natDigitBytes nw.toNat ++ 32 :: (natDigitBytes ne.toNat ++
        32 :: (natDigitBytes sw.toNat ++ 32 :: natDigitBytes se.toNat))) := by
  show (toString level.toNat ++ " " ++ toString nw.toNat ++ " " ++ toString ne.toNat ++ " " ++ toString sw.toNat ++
    " " ++ toString se.toNat).toByteArray.data.toList = _
  simp only [String.toByteArray_append, byteArray_append_toList, Nat.toString_eq_repr, bytes_natRepr,
    List.append_assoc]
  rfl

/-- A node line written by the serializer parses back to its level and children. -/
theorem parseMCNodeLine_format (level nw ne sw se : UInt32) :
    ∃ n, parseMCNodeLine (formatMacrocellNode level nw ne sw se).toByteArray = some n ∧
      n.level = level ∧ n.nw = nw ∧ n.ne = ne ∧ n.sw = sw ∧ n.se = se := by
  rw [byteArray_eq_of_toList (bytes_formatMacrocellNode level nw ne sw se)]
  have h0 := natDigitBytes_length_le level.toNat (by have := UInt32.toNat_lt level; omega)
  have h1 := natDigitBytes_length_le nw.toNat (by have := UInt32.toNat_lt nw; omega)
  have h2 := natDigitBytes_length_le ne.toNat (by have := UInt32.toNat_lt ne; omega)
  have h3 := natDigitBytes_length_le sw.toNat (by have := UInt32.toNat_lt sw; omega)
  have h4 := natDigitBytes_length_le se.toNat (by have := UInt32.toNat_lt se; omega)
  generalize hD0 : natDigitBytes level.toNat = D0 at h0
  generalize hD1 : natDigitBytes nw.toNat = D1 at h1
  generalize hD2 : natDigitBytes ne.toNat = D2 at h2
  generalize hD3 : natDigitBytes sw.toNat = D3 at h3
  generalize hD4 : natDigitBytes se.toNat = D4 at h4
  generalize hLL : D0 ++ 32 :: (D1 ++ 32 :: (D2 ++ 32 :: (D3 ++ 32 :: D4))) = L
  have hLlen : L.length = D0.length + D1.length + D2.length + D3.length + D4.length + 4 := by
    rw [← hLL]; simp; omega
  have hL : L.length < 2 ^ 32 := by omega
  have hidx : ∀ k, k ≤ L.length → k.toUInt32.toNat = k := fun k hk => u32_size_toNat (by omega)
  have nd : ∀ y, ([32] : List UInt8).head? = some y → isDigitByte y = false := by
    intro y hy; simp at hy; subst hy; decide
  have nd' : ∀ (R : List UInt8) y, (32 :: R).head? = some y → isDigitByte y = false := by
    intro R y hy; simp at hy; subst hy; decide
  have S1 : L.drop D0.length = 32 :: (D1 ++ 32 :: (D2 ++ 32 :: (D3 ++ 32 :: D4))) := by
    rw [← hLL, List.drop_left' rfl]
  have S2 := drop_sep D1 L _ S1
  have S3 := drop_sep D2 L _ S2
  have S4 := drop_sep D3 L _ S3
  have e0 := skipParse_list L hL 0 0 0 rfl level (32 :: (D1 ++ 32 :: (D2 ++ 32 :: (D3 ++ 32 :: D4))))
    (by rw [← hLL, ← hD0]; rfl) (nd' _)
  have e1 := skipParse_list L hL _ D0.length 1 (by rw [← hD0]; exact hidx _ (by rw [hD0]; omega)) nw
    (32 :: (D2 ++ 32 :: (D3 ++ 32 :: D4))) (by rw [S1, ← hD1]; rfl) (nd' _)
  have e2 := skipParse_list L hL _ (D0.length + 1 + D1.length) 1 (by rw [← hD1]; exact hidx _ (by rw [hD1]; omega))
    ne (32 :: (D3 ++ 32 :: D4)) (by rw [S2, ← hD2]; rfl) (nd' _)
  have e3 := skipParse_list L hL _ (D0.length + 1 + D1.length + 1 + D2.length) 1
    (by rw [← hD2]; exact hidx _ (by rw [hD2]; omega)) sw (32 :: D4) (by rw [S3, ← hD3]; rfl) (nd' _)
  have e4 := skipParse_list L hL _ (D0.length + 1 + D1.length + 1 + D2.length + 1 + D3.length) 1
    (by rw [← hD3]; exact hidx _ (by rw [hD3]; omega)) se [] (by rw [S4, ← hD4]; simp) (by simp)
  simp only [hD0, hD1, hD2, hD3, hD4, Nat.add_zero, Nat.zero_add] at e0 e1 e2 e3 e4
  have hend : skipSpaces ⟨L.toArray⟩ (D0.length + 1 + D1.length + 1 + D2.length + 1 + D3.length + 1 + D4.length).toUInt32
      (⟨L.toArray⟩ : ByteArray).size.toUInt32 = (⟨L.toArray⟩ : ByteArray).size.toUInt32 := by
    have := skipSpaces_list L hL _ (D0.length + 1 + D1.length + 1 + D2.length + 1 + D3.length + 1 + D4.length) 0
      (hidx _ (by omega)) (by omega) [] (by rw [List.drop_eq_nil_of_le (by omega)]; rfl) (by simp)
    rw [this, size_of_list]; congr 1; omega
  unfold parseMCNodeLine
  simp only [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, hend, beq_self_eq_true, ite_true]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Leaf lines -/

/-- What reading leaf line bytes does to the leaf, from cell (`x`, `y`). -/
def leafDecode : List UInt8 → UInt32 → UInt32 → UInt64 → UInt64
  | [], _, _, l => l
  | c :: cs, x, y, l =>
    if c = 36 then leafDecode cs 0 (y + 1) l
    else leafDecode cs (x + 1) y (if c = 42 ∧ x < 8 ∧ y < 8 then leafWithCell l x y true else l)

/-- A leaf line of `.`, `*` and `$` is read without warnings, then its leaf is added. -/
theorem loop_leaf (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (B : ByteArray)
    (hB : B.size < 2 ^ 32) (hok : ∀ k, k < B.size → B[k]! = 36 ∨ B[k]! = 42 ∨ B[k]! = 46) :
    ∀ (n : Nat) (p col x y : UInt32) (l : UInt64) (nodes : GrowBuf MacroCell) (leaves : GrowBuf UInt64)
      (isLeaf : GrowBuf Bool) (warns : GrowBuf MacrocellWarning), B.size - p.toNat = n → p.toNat ≤ B.size →
      deserializeMacrocell.loop lines numLines i true B B.size.toUInt32 p col x y l nodes leaves isLeaf warns =
        deserializeMacrocell.loop lines numLines (i + 1) false B B.size.toUInt32 0 0 0 0 0
          (nodes.push (makeLevel4Node (leafDecode (bytesFrom B p.toNat) x y l) 0 0 0))
          (leaves.push (leafDecode (bytesFrom B p.toNat) x y l)) (isLeaf.push true) warns := by
  intro n
  induction n with
  | zero =>
    intro p col x y l nodes leaves isLeaf warns hn hp
    have hnot : ¬ p < B.size.toUInt32 := by rw [u32_lt_size_iff hB]; omega
    have hnil : bytesFrom B p.toNat = [] := by
      unfold bytesFrom; apply List.drop_eq_nil_of_le; simp; omega
    rw [deserializeMacrocell.loop]
    simp only [hi, ↓reduceDIte, ite_true, hnot, hnil, leafDecode]
  | succ n ih =>
    intro p col x y l nodes leaves isLeaf warns hn hp
    have hlt : p < B.size.toUInt32 := by rw [u32_lt_size_iff hB]; omega
    have hpn : p.toNat < B.size := by omega
    have hsucc : (p + 1).toNat = p.toNat + 1 := by
      rw [UInt32.toNat_add]; simp; omega
    have hget : B.get! p.toNat = B[p.toNat]! := by rw [byteArray_get!_eq hpn, getElem!_pos B _ hpn]
    have hb := hok _ hpn
    have hasc : B.get! p.toNat < 128 := by rw [hget]; rcases hb with h | h | h <;> rw [h] <;> decide
    have hcons : bytesFrom B p.toNat = B[p.toNat]! :: bytesFrom B (p.toNat + 1) := by
      rw [bytesFrom_of_lt hpn, getElem!_pos B _ hpn]
    rw [deserializeMacrocell.loop]
    simp only [hi, ↓reduceDIte, ite_true, hlt, decodeCharAt_ascii B p _ hasc, hget, hcons, leafDecode]
    rw [← hsucc]
    rcases hb with h | h | h <;> rw [h]
    · simp only [show ((36 : UInt8).toUInt32 == 36) = true from rfl, ite_true]
      exact ih _ _ _ _ _ _ _ _ _ (by omega) (by omega)
    · simp only [show ((42 : UInt8).toUInt32 == 36) = false from rfl, Bool.false_eq_true, ite_false,
        show ((42 : UInt8).toUInt32 == 42) = true from rfl, show ((42 : UInt8).toUInt32 != 46) = true from rfl,
        show ((42 : UInt8).toUInt32 != 42) = false from rfl, Bool.and_false, Bool.true_and, true_and,
        show ((42 : UInt8) = 36) = False from by decide]
      rw [show (if (decide (x < 8) && decide (y < 8)) = true then leafWithCell l x y true else l) =
        (if x < 8 ∧ y < 8 then leafWithCell l x y true else l) by simp]
      exact ih _ _ _ _ _ _ _ _ _ (by omega) (by omega)
    · simp only [show ((46 : UInt8).toUInt32 == 36) = false from rfl, Bool.false_eq_true, ite_false,
        show ((46 : UInt8).toUInt32 == 42) = false from rfl, show ((46 : UInt8).toUInt32 != 46) = false from rfl,
        Bool.false_and, show ((46 : UInt8) = 36) = False from by decide, show ((46 : UInt8) = 42) = False from by decide,
        false_and]
      exact ih _ _ _ _ _ _ _ _ _ (by omega) (by omega)

/-- Whether a `*` of leaf line bytes, read from cell (`x`, `y`), lands on cell (`X`, `Y`) of the leaf. -/
def starAt : List UInt8 → UInt32 → UInt32 → Nat → Nat → Bool
  | [], _, _, _, _ => false
  | c :: cs, x, y, X, Y =>
    if c = 36 then starAt cs 0 (y + 1) X Y
    else decide (c = 42 ∧ x < 8 ∧ y < 8 ∧ x.toNat = X ∧ y.toNat = Y) || starAt cs (x + 1) y X Y

theorem leafAt_leafDecode (X Y : Nat) :
    ∀ (cs : List UInt8) (x y : UInt32) (l : UInt64),
      leafAt (leafDecode cs x y l) X Y = (leafAt l X Y || starAt cs x y X Y) := by
  intro cs
  induction cs with
  | nil => intro x y l; simp [leafDecode, starAt]
  | cons c cs ih =>
    intro x y l
    unfold leafDecode starAt
    by_cases h36 : c = 36
    · simp only [h36, ite_true]; exact ih _ _ _
    · simp only [h36, ite_false, ih]
      by_cases hc : c = 42 ∧ x < 8 ∧ y < 8
      · rw [ite_eq_left hc, leafAt_leafWithCell l x y (UInt32.lt_iff_toNat_lt.mp hc.2.1)
          (UInt32.lt_iff_toNat_lt.mp hc.2.2)]
        by_cases hxy : x.toNat = X ∧ y.toNat = Y
        · have : (X : Int) = x.toNat ∧ (Y : Int) = y.toNat := ⟨by omega, by omega⟩
          rw [ite_eq_left this]
          simp [hc, hxy]
        · have : ¬ ((X : Int) = x.toNat ∧ (Y : Int) = y.toNat) := fun h => hxy ⟨by omega, by omega⟩
          rw [ite_eq_right this]
          simp [hxy]
      · rw [ite_eq_right hc]
        have : ¬ (c = 42 ∧ x < 8 ∧ y < 8 ∧ x.toNat = X ∧ y.toNat = Y) := fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩
        simp [this]

theorem string_push_bytes (s : String) (c : Char) :
    (s.push c).toByteArray.data.toList = s.toByteArray.data.toList ++ (String.singleton c).toByteArray.data.toList := by
  rw [← String.append_singleton, String.toByteArray_append, byteArray_append_toList]

/-- The byte of cell `x` of row `y` of a leaf. -/
def leafCellByte (leaf : UInt64) (y : UInt32) (x : Nat) : UInt8 := if leafContains leaf x.toUInt32 y then 42 else 46

/-- The bytes of row `y` of a leaf line, without its `$`. -/
def leafRowBytes (leaf : UInt64) (y : UInt32) : List UInt8 :=
  match findLastLeafX leaf y with
  | none => []
  | some lastX => (List.range' 0 (lastX.toNat + 1)).map (leafCellByte leaf y)

/-- The bytes of a leaf line. -/
def leafLineBytes (leaf : UInt64) : List UInt8 :=
  match findLastLeafRow leaf with
  | none => [36]
  | some lastY => (List.range' 0 (lastY.toNat + 1)).flatMap (fun y => leafRowBytes leaf y.toUInt32 ++ [36])

theorem findLastLeafX_lt (leaf : UInt64) (y lx : UInt32) (h : findLastLeafX leaf y = some lx) : lx.toNat < 8 := by
  unfold findLastLeafX at h
  repeat' split at h
  all_goals first | (simp only [Option.some.injEq] at h; subst h; decide) | simp at h

theorem findLastLeafRow_lt (leaf : UInt64) (ly : UInt32) (h : findLastLeafRow leaf = some ly) : ly.toNat < 8 := by
  unfold findLastLeafRow at h
  repeat' split at h
  all_goals first | (simp only [Option.some.injEq] at h; subst h; decide) | simp at h

theorem formatLeafRow_loop_bytes (leaf : UInt64) (y : UInt32) :
    ∀ (n : Nat) (x limit : UInt32) (acc : String), limit.toNat - x.toNat = n → limit.toNat ≤ 8 →
      (formatLeafRow.loop leaf y x limit acc).toByteArray.data.toList =
        acc.toByteArray.data.toList ++ (List.range' x.toNat n).map (leafCellByte leaf y) := by
  intro n
  induction n with
  | zero =>
    intro x limit acc hn hl
    rw [formatLeafRow.loop, dite_eq_right_iff.mpr (fun h => absurd (UInt32.lt_iff_toNat_lt.mp h) (by omega))]
    simp
  | succ n ih =>
    intro x limit acc hn hl
    have hlt : x < limit := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (x + 1).toNat = x.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    rw [formatLeafRow.loop, dite_eq_left_of_eq_true (by simp [hlt])]
    rw [ih _ _ _ (by omega) hl, string_push_bytes, hsucc, List.range'_succ]
    have hx : x.toNat.toUInt32 = x := by simp
    simp only [List.map_cons, List.append_assoc, leafCellByte, hx]
    congr 1
    split <;> rfl

theorem formatLeafRow_bytes (leaf : UInt64) (y : UInt32) :
    (formatLeafRow leaf y).toByteArray.data.toList = leafRowBytes leaf y := by
  unfold formatLeafRow leafRowBytes
  cases hlx : findLastLeafX leaf y with
  | none => rfl
  | some lx =>
    have := findLastLeafX_lt leaf y lx hlx
    have h1 : (lx + 1).toNat = lx.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    simp only
    rw [formatLeafRow_loop_bytes leaf y (lx.toNat + 1) 0 (lx + 1) "" (by simp [h1]) (by omega)]
    simp

theorem formatLeafNode_loop_bytes (leaf : UInt64) :
    ∀ (n : Nat) (y limit : UInt32) (acc : String), limit.toNat - y.toNat = n → limit.toNat ≤ 8 →
      (formatLeafNode.loop leaf y limit acc).toByteArray.data.toList =
        acc.toByteArray.data.toList ++
          (List.range' y.toNat n).flatMap (fun k => leafRowBytes leaf k.toUInt32 ++ [36]) := by
  intro n
  induction n with
  | zero =>
    intro y limit acc hn hl
    rw [formatLeafNode.loop, dite_eq_right_iff.mpr (fun h => absurd (UInt32.lt_iff_toNat_lt.mp h) (by omega))]
    simp
  | succ n ih =>
    intro y limit acc hn hl
    have hlt : y < limit := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (y + 1).toNat = y.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    rw [formatLeafNode.loop, dite_eq_left_of_eq_true (by simp [hlt])]
    rw [ih _ _ _ (by omega) hl, String.toByteArray_append, String.toByteArray_append, byteArray_append_toList,
      byteArray_append_toList, formatLeafRow_bytes, hsucc, List.range'_succ]
    have hy : y.toNat.toUInt32 = y := by simp
    simp only [List.flatMap_cons, List.append_assoc, hy]
    rfl

theorem formatLeafNode_bytes (leaf : UInt64) :
    (formatLeafNode leaf).toByteArray.data.toList = leafLineBytes leaf := by
  unfold formatLeafNode leafLineBytes
  cases hly : findLastLeafRow leaf with
  | none => rfl
  | some ly =>
    have := findLastLeafRow_lt leaf ly hly
    have h1 : (ly + 1).toNat = ly.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    simp only
    rw [formatLeafNode_loop_bytes leaf (ly.toNat + 1) 0 (ly + 1) "" (by simp [h1]) (by omega)]
    simp

theorem nat_toUInt32_lits : (0 : Nat).toUInt32 = 0 ∧ (1 : Nat).toUInt32 = 1 ∧ (2 : Nat).toUInt32 = 2 ∧
    (3 : Nat).toUInt32 = 3 ∧ (4 : Nat).toUInt32 = 4 ∧ (5 : Nat).toUInt32 = 5 ∧ (6 : Nat).toUInt32 = 6 ∧
    (7 : Nat).toUInt32 = 7 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nat_lt8_cases (x : Nat) (h : x < 8) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega

theorem findLastLeafX_none (leaf : UInt64) (y : UInt32) (h : findLastLeafX leaf y = none) :
    ∀ x : Nat, x < 8 → leafContains leaf x.toUInt32 y = false := by
  intro x hx
  unfold findLastLeafX at h
  repeat' split at h
  all_goals try simp at h
  rcases nat_lt8_cases x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [nat_toUInt32_lits]

theorem findLastLeafX_some (leaf : UInt64) (y lx : UInt32) (h : findLastLeafX leaf y = some lx) :
    ∀ x : Nat, lx.toNat < x → x < 8 → leafContains leaf x.toUInt32 y = false := by
  intro x hlx hx
  unfold findLastLeafX at h
  repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals rcases nat_lt8_cases x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp at hlx; done) | simp_all [nat_toUInt32_lits]

theorem findLastLeafRow_none (leaf : UInt64) (h : findLastLeafRow leaf = none) :
    ∀ y : Nat, y < 8 → findLastLeafX leaf y.toUInt32 = none := by
  intro y hy
  unfold findLastLeafRow at h
  repeat' split at h
  all_goals try simp at h
  rcases nat_lt8_cases y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [nat_toUInt32_lits]

theorem findLastLeafRow_some (leaf : UInt64) (ly : UInt32) (h : findLastLeafRow leaf = some ly) :
    ∀ y : Nat, ly.toNat < y → y < 8 → findLastLeafX leaf y.toUInt32 = none := by
  intro y hly hy
  unfold findLastLeafRow at h
  repeat' split at h
  all_goals simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals rcases nat_lt8_cases y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp at hly; done) | simp_all [nat_toUInt32_lits]

theorem starAt_cons_ne (c : UInt8) (cs : List UInt8) (x y : UInt32) (X Y : Nat) (h : c ≠ 36) :
    starAt (c :: cs) x y X Y =
      (decide (c = 42 ∧ x < 8 ∧ y < 8 ∧ x.toNat = X ∧ y.toNat = Y) || starAt cs (x + 1) y X Y) := by
  rw [starAt, ite_eq_right h]

theorem starAt_cons_end (cs : List UInt8) (x y : UInt32) (X Y : Nat) :
    starAt (36 :: cs) x y X Y = starAt cs 0 (y + 1) X Y := by
  rw [starAt, ite_eq_left rfl]

theorem starAt_row (leaf : UInt64) (y : UInt32) (hy : y.toNat < 8) (X Y : Nat) :
    ∀ (n a : Nat), a + n ≤ 8 → ∀ rest : List UInt8,
      starAt ((List.range' a n).map (leafCellByte leaf y) ++ rest) a.toUInt32 y X Y =
        (decide (Y = y.toNat ∧ a ≤ X ∧ X < a + n ∧ leafContains leaf X.toUInt32 y = true) ||
          starAt rest (a + n).toUInt32 y X Y) := by
  intro n
  induction n with
  | zero => intro a _ rest; simp; intro _ _ _; omega
  | succ n ih =>
    intro a ha rest
    rw [List.range'_succ, List.map_cons, List.cons_append]
    have hne : leafCellByte leaf y a ≠ 36 := by unfold leafCellByte; split <;> decide
    rw [starAt_cons_ne _ _ _ _ _ _ hne]
    have ha1 : a.toUInt32 + 1 = (a + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp
    rw [ha1, ih (a + 1) (by omega) rest, show a + 1 + n = a + (n + 1) by omega]
    generalize starAt rest (a + (n + 1)).toUInt32 y X Y = R
    have hat : a.toUInt32.toNat = a := u32_size_toNat (by omega)
    have hlt : a.toUInt32 < 8 := UInt32.lt_iff_toNat_lt.mpr (by rw [hat]; simp; omega)
    have hylt : y < 8 := UInt32.lt_iff_toNat_lt.mpr (by simp; omega)
    have hc42 : leafCellByte leaf y a = 42 ↔ leafContains leaf a.toUInt32 y = true := by
      unfold leafCellByte; split <;> simp_all
    rw [hat]
    by_cases hX : X = a
    · subst hX
      by_cases hc : leafContains leaf X.toUInt32 y = true <;> by_cases hY : Y = y.toNat <;>
        simp [hc, hY, hlt, hylt, hc42, eq_comm]
    · have hX' : a ≠ X := fun h => hX h.symm
      simp only [hX', false_and, and_false, decide_false, Bool.false_or]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by omega, by omega, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by omega, by omega, h4⟩

theorem starAt_rowEnd (leaf : UInt64) (y : UInt32) (hy : y.toNat < 8) (X Y : Nat) (hX : X < 8)
    (rest : List UInt8) :
    starAt (leafRowBytes leaf y ++ 36 :: rest) 0 y X Y =
      (decide (Y = y.toNat ∧ leafContains leaf X.toUInt32 y = true) || starAt rest 0 (y + 1) X Y) := by
  unfold leafRowBytes
  cases hlx : findLastLeafX leaf y with
  | none =>
    simp only [List.nil_append, starAt_cons_end, findLastLeafX_none leaf y hlx X hX]
    simp
  | some lx =>
    have hlt := findLastLeafX_lt leaf y lx hlx
    have := starAt_row leaf y hy X Y (lx.toNat + 1) 0 (by omega) (36 :: rest)
    simp only [show (0 : Nat).toUInt32 = 0 from rfl, Nat.zero_add, starAt_cons_end] at this
    simp only
    rw [this]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨h1, -, -, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩
      refine ⟨h1, Nat.zero_le _, ?_, h4⟩
      refine Nat.lt_of_not_le (fun hc => ?_)
      have := findLastLeafX_some leaf y lx hlx X (by omega) hX
      simp_all

theorem starAt_rows (leaf : UInt64) (X Y : Nat) (hX : X < 8) :
    ∀ (m y0 : Nat), y0 + m ≤ 8 → ∀ rest : List UInt8,
      starAt ((List.range' y0 m).flatMap (fun k => leafRowBytes leaf k.toUInt32 ++ [36]) ++ rest) 0 y0.toUInt32 X Y =
        (decide (y0 ≤ Y ∧ Y < y0 + m ∧ leafContains leaf X.toUInt32 Y.toUInt32 = true) ||
          starAt rest 0 (y0 + m).toUInt32 X Y) := by
  intro m
  induction m with
  | zero => intro y0 _ rest; simp; intro _ _; omega
  | succ m ih =>
    intro y0 hm rest
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.append_assoc, List.singleton_append]
    have hy0 : y0.toUInt32.toNat = y0 := u32_size_toNat (by omega)
    rw [starAt_rowEnd leaf _ (by omega) X Y hX]
    have h1 : y0.toUInt32 + 1 = (y0 + 1).toUInt32 := by
      apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add]; simp
    rw [h1, ih (y0 + 1) (by omega) rest, show y0 + 1 + m = y0 + (m + 1) by omega, hy0]
    generalize starAt rest 0 (y0 + (m + 1)).toUInt32 X Y = R
    by_cases hY : Y = y0
    · subst hY
      by_cases hc : leafContains leaf X.toUInt32 Y.toUInt32 = true <;> simp [hc]
    · have hY' : ¬ (Y = y0 ∧ leafContains leaf X.toUInt32 y0.toUInt32 = true) := fun h => hY h.1
      simp only [hY', decide_false, Bool.false_or]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩

theorem mortonIndex_surj : ∀ i < 64, ∃ x < 8, ∃ y < 8, mortonIndex x y = i := by decide

/-- Leaves with the same cells are equal. -/
theorem leaf_ext (a b : UInt64) (h : ∀ x y : Nat, x < 8 → y < 8 → leafAt a x y = leafAt b x y) : a = b := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨x, hx, y, hy, rfl⟩ := mortonIndex_surj i hi
  have := h x y hx hy
  unfold leafAt at this
  simpa [show (0 : Int) ≤ x by omega, show (x : Int) < 8 by omega, show (0 : Int) ≤ y by omega,
    show (y : Int) < 8 by omega] using this

theorem leafAt_zero' (X Y : Int) : leafAt 0 X Y = false := by
  unfold leafAt; split <;> simp

theorem leafAt_eq_contains (leaf : UInt64) (X Y : Nat) (hX : X < 8) (hY : Y < 8) :
    leafAt leaf X Y = leafContains leaf X.toUInt32 Y.toUInt32 := by
  rw [leafContains_toNat leaf _ _ (by rw [u32_size_toNat (by omega)]; exact hX)
    (by rw [u32_size_toNat (by omega)]; exact hY), u32_size_toNat (by omega), u32_size_toNat (by omega)]

/-- Reading a formatted leaf line gives back the leaf. -/
theorem leafDecode_format (leaf : UInt64) : leafDecode (leafLineBytes leaf) 0 0 0 = leaf := by
  apply leaf_ext
  intro X Y hX hY
  rw [leafAt_leafDecode, leafAt_zero', Bool.false_or, leafAt_eq_contains leaf X Y hX hY]
  unfold leafLineBytes
  cases hly : findLastLeafRow leaf with
  | none =>
    rw [findLastLeafX_none leaf _ (findLastLeafRow_none leaf hly Y hY) X hX]
    simp [starAt]
  | some ly =>
    have hlt := findLastLeafRow_lt leaf ly hly
    have := starAt_rows leaf X Y hX (ly.toNat + 1) 0 (by omega) []
    simp only [show (0 : Nat).toUInt32 = 0 from rfl, List.append_nil, Nat.zero_add, starAt, Bool.or_false,
      Nat.zero_le, true_and] at this
    simp only
    rw [this]
    by_cases hc : leafContains leaf X.toUInt32 Y.toUInt32 = true
    · have : Y < ly.toNat + 1 := by
        refine Nat.lt_of_not_le (fun hn => ?_)
        rw [findLastLeafX_none leaf _ (findLastLeafRow_some leaf ly hly Y (by omega) hY) X hX] at hc
        simp at hc
      simp [hc, this]
    · simp [hc]

theorem flatMap_range'_length_le (f : Nat → List UInt8) (c : Nat) (hf : ∀ k, (f k).length ≤ c) :
    ∀ n a, ((List.range' a n).flatMap f).length ≤ c * n := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range'_succ, List.flatMap_cons, List.length_append, Nat.mul_succ]
    have := hf a; have := ih (a + 1); omega

theorem leafRowBytes_length (leaf : UInt64) (y : UInt32) : (leafRowBytes leaf y).length ≤ 8 := by
  unfold leafRowBytes
  cases hlx : findLastLeafX leaf y with
  | none => simp
  | some lx => have := findLastLeafX_lt leaf y lx hlx; simp; omega

theorem leafLineBytes_length (leaf : UInt64) : (leafLineBytes leaf).length ≤ 72 := by
  unfold leafLineBytes
  cases hly : findLastLeafRow leaf with
  | none => simp
  | some ly =>
    have := findLastLeafRow_lt leaf ly hly
    have := flatMap_range'_length_le (fun y => leafRowBytes leaf y.toUInt32 ++ [36]) 9
      (fun k => by simp only [List.length_append, List.length_singleton]; have := leafRowBytes_length leaf k.toUInt32; omega)
      (ly.toNat + 1) 0
    simp only
    omega

theorem leafLineBytes_mem (leaf : UInt64) : ∀ b ∈ leafLineBytes leaf, b = 36 ∨ b = 42 ∨ b = 46 := by
  have hrow : ∀ y, ∀ b ∈ leafRowBytes leaf y, b = 42 ∨ b = 46 := by
    intro y b hb
    unfold leafRowBytes at hb
    split at hb
    · simp at hb
    · simp only [List.mem_map] at hb
      obtain ⟨x, -, rfl⟩ := hb
      unfold leafCellByte; split <;> simp
  intro b hb
  unfold leafLineBytes at hb
  split at hb
  · simp at hb; simp [hb]
  · simp only [List.mem_flatMap, List.mem_append, List.mem_singleton] at hb
    obtain ⟨y, -, hb | hb⟩ := hb
    · rcases hrow _ b hb with h | h <;> simp [h]
    · simp [hb]

theorem leafLineBytes_ne_nil (leaf : UInt64) : leafLineBytes leaf ≠ [] := by
  unfold leafLineBytes
  split
  · simp
  · rw [List.range'_succ, List.flatMap_cons]; simp

/-- A leaf line adds its leaf. -/
theorem loop_leafLine (lines : Array String) (numLines i : UInt32) (hi : i < numLines) (leaf : UInt64)
    (hline : lines[i.toNat]! = formatLeafNode leaf) (B : ByteArray) (lim p col x y : UInt32) (l : UInt64)
    (nodes : GrowBuf MacroCell) (leaves : GrowBuf UInt64) (isLeaf : GrowBuf Bool) (warns : GrowBuf MacrocellWarning) :
    deserializeMacrocell.loop lines numLines i false B lim p col x y l nodes leaves isLeaf warns =
      deserializeMacrocell.loop lines numLines (i + 1) false (formatLeafNode leaf).toByteArray
        (formatLeafNode leaf).toByteArray.size.toUInt32 0 0 0 0 0
        (nodes.push (makeLevel4Node leaf 0 0 0)) (leaves.push leaf) (isLeaf.push true) warns := by
  have hB := byteArray_eq_of_toList (formatLeafNode_bytes leaf)
  have hlen := leafLineBytes_length leaf
  have hmem := leafLineBytes_mem leaf
  have hne := leafLineBytes_ne_nil leaf
  have hsz : (formatLeafNode leaf).toByteArray.size = (leafLineBytes leaf).length := by rw [hB, size_of_list]
  have hok : ∀ k, k < (formatLeafNode leaf).toByteArray.size → (formatLeafNode leaf).toByteArray[k]! = 36 ∨
      (formatLeafNode leaf).toByteArray[k]! = 42 ∨ (formatLeafNode leaf).toByteArray[k]! = 46 := by
    intro k hk
    have e : (formatLeafNode leaf).toByteArray[k]! = (formatLeafNode leaf).toByteArray.get! k := by
      rw [byteArray_get!_eq hk, getElem!_pos _ k hk]
    rw [hsz] at hk
    have := get!_of_list (leafLineBytes leaf) k hk
    rw [← hB] at this
    rw [e, this]
    rw [getElem!_pos _ k hk]
    exact hmem _ (List.getElem_mem hk)
  have hpos : 0 < (leafLineBytes leaf).length := List.length_pos_iff.mpr hne
  have hpos' : 0 < (formatLeafNode leaf).toByteArray.size := by omega
  have h0 := hok 0 hpos'
  have hg0 : (formatLeafNode leaf).toByteArray.get! 0 = (formatLeafNode leaf).toByteArray[0]! := by
    rw [byteArray_get!_eq hpos', getElem!_pos _ 0 hpos']
  rw [deserializeMacrocell.loop]
  simp only [hi, ↓reduceDIte, Bool.false_eq_true, ite_false, hline]
  have hl0 : ((formatLeafNode leaf).toByteArray.size.toUInt32 == 0) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt32.toNat_inj, u32_size_toNat (by omega), UInt32.toNat_zero]; omega
  have h35 : ((formatLeafNode leaf).toByteArray.get! 0 == 35) = false := by
    rw [hg0]; rcases h0 with h | h | h <;> rw [h] <;> decide
  have hdig : isDigitByte ((formatLeafNode leaf).toByteArray.get! 0) = false := by
    rw [hg0]; rcases h0 with h | h | h <;> rw [h] <;> decide
  simp only [hl0, h35, hdig, Bool.false_eq_true, ite_false]
  rw [loop_leaf lines numLines i hi _ (by omega) hok _ 0 0 0 0 0 nodes leaves isLeaf warns rfl (by simp)]
  have : leafDecode (bytesFrom (formatLeafNode leaf).toByteArray (0 : UInt32).toNat) 0 0 0 = leaf := by
    rw [UInt32.toNat_zero, hB, bytesFrom_of_list, List.drop_zero, leafDecode_format]
  rw [this]

theorem formatMacrocellNode_first (level nw ne sw se : UInt32) :
    0 < (formatMacrocellNode level nw ne sw se).toByteArray.size ∧
      isDigitByte ((formatMacrocellNode level nw ne sw se).toByteArray.get! 0) = true ∧
      (formatMacrocellNode level nw ne sw se).toByteArray.size < 2 ^ 32 := by
  have hB := byteArray_eq_of_toList (bytes_formatMacrocellNode level nw ne sw se)
  obtain ⟨hd, -, hne⟩ := natDigitBytes_spec level.toNat
  have h0 := natDigitBytes_length_le level.toNat (by have := UInt32.toNat_lt level; omega)
  have h1 := natDigitBytes_length_le nw.toNat (by have := UInt32.toNat_lt nw; omega)
  have h2 := natDigitBytes_length_le ne.toNat (by have := UInt32.toNat_lt ne; omega)
  have h3 := natDigitBytes_length_le sw.toNat (by have := UInt32.toNat_lt sw; omega)
  have h4 := natDigitBytes_length_le se.toNat (by have := UInt32.toNat_lt se; omega)
  rw [hB, size_of_list]
  cases hD : natDigitBytes level.toNat with
  | nil => exact absurd hD hne
  | cons z zs =>
    refine ⟨by simp, ?_, ?_⟩
    · rw [get!_of_list _ 0 (by simp)]
      simp only [List.cons_append, List.getElem!_cons_zero]
      exact (isDigitByte_iff _).mpr (hd z (by rw [hD]; simp))
    · rw [hD] at h0; simp only [List.length_append, List.length_cons] at h0 ⊢; omega

/-- The array view of `macrocellLeafChild`. -/
def leafChildA (leaves : Array UInt64) (isLeaf : Array Bool) (id : UInt32) : Option UInt64 :=
  if id == 0 then some 0
  else if id.toNat > isLeaf.size then none
  else if isLeaf[(id - 1).toNat]! then some leaves[(id - 1).toNat]!
  else none

/-- The array view of `macrocellCellChild`. -/
def cellChildA (nodes : Array MacroCell) (isLeaf : Array Bool) (level : UInt32) (emptySub : MacroCell) (id : UInt32) :
    Option MacroCell :=
  if id == 0 then some emptySub
  else if id.toNat > isLeaf.size then none
  else if isLeaf[(id - 1).toNat]! then none
  else
    let e := macroCellAt nodes (id - 1)
    if e.level + 1 == level then some e else none

theorem rep_getElem! {α : Type} [Inhabited α] {b : GrowBuf α} {a : Array α} (h : b.Rep a) (k : Nat) (hk : k < a.size) :
    b.data[k]! = a[k]! := by
  obtain ⟨hs, hle, -, harr⟩ := h
  rw [← harr]
  unfold GrowBuf.toArray
  rw [getElem!_pos b.data k (by omega), getElem!_pos _ k (by simp; omega)]
  simp

theorem macrocellLeafChild_eq {leaves : GrowBuf UInt64} {isLeaf : GrowBuf Bool} {Lv : Array UInt64} {IL : Array Bool}
    (hl : leaves.Rep Lv) (hi : isLeaf.Rep IL) (hsz : IL.size ≤ Lv.size) (id : UInt32) :
    macrocellLeafChild leaves isLeaf id = leafChildA Lv IL id := by
  unfold macrocellLeafChild leafChildA
  have hs : isLeaf.size.toNat = IL.size := hi.1
  by_cases h0 : id = 0
  · simp [h0]
  · have h0' : (id == 0) = false := by simp [h0]
    have hid : 1 ≤ id.toNat := by
      have : id.toNat ≠ 0 := fun h => h0 (UInt32.toNat_inj.mp (by rw [h]; rfl)); omega
    have hsub : (id - 1).toNat = id.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
    simp only [h0', Bool.false_eq_true, ite_false, gt_iff_lt, UInt32.lt_iff_toNat_lt, hs]
    by_cases hgt : IL.size < id.toNat
    · simp [hgt]
    · simp only [hgt, ite_false]
      rw [rep_getElem! hi _ (by omega), rep_getElem! hl _ (by omega)]

theorem macrocellCellChild_eq {nodes : GrowBuf MacroCell} {isLeaf : GrowBuf Bool} {N : Array MacroCell}
    {IL : Array Bool} (hn : nodes.Rep N) (hi : isLeaf.Rep IL) (hsz : IL.size ≤ N.size) (level : UInt32)
    (emptySub : MacroCell) (id : UInt32) :
    macrocellCellChild nodes isLeaf level emptySub id = cellChildA N IL level emptySub id := by
  unfold macrocellCellChild cellChildA macroCellAt
  have hs : isLeaf.size.toNat = IL.size := hi.1
  by_cases h0 : id = 0
  · simp [h0]
  · have h0' : (id == 0) = false := by simp [h0]
    have hid : 1 ≤ id.toNat := by
      have : id.toNat ≠ 0 := fun h => h0 (UInt32.toNat_inj.mp (by rw [h]; rfl)); omega
    have hsub : (id - 1).toNat = id.toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
    simp only [h0', Bool.false_eq_true, ite_false, gt_iff_lt, UInt32.lt_iff_toNat_lt, hs]
    by_cases hgt : IL.size < id.toNat
    · simp [hgt]
    · simp only [hgt, ite_false]
      rw [rep_getElem! hi _ (by omega), rep_getElem! hn _ (by omega)]

theorem loop_nodeLine_prefix (lines : Array String) (numLines i : UInt32) (hi : i < numLines)
    (level a b c d : UInt32) (hline : lines[i.toNat]! = formatMacrocellNode level a b c d)
    (B : ByteArray) (lim p col x y : UInt32) (l : UInt64)
    (nodes : GrowBuf MacroCell) (leaves : GrowBuf UInt64) (isLeaf : GrowBuf Bool) (warns : GrowBuf MacrocellWarning) :
    ∃ n : MCNodeLine, n.level = level ∧ n.nw = a ∧ n.ne = b ∧ n.sw = c ∧ n.se = d ∧
      deserializeMacrocell.loop lines numLines i false B lim p col x y l nodes leaves isLeaf warns =
        (if n.level < 4 || n.level > maxMacrocellLevel then
          (⟨.unexpectedInput (formatMacrocellNode level a b c d) i, warns.toArray, emptyLevel4⟩ : MacrocellResult)
        else if n.level == 4 then
          match macrocellLeafChild leaves isLeaf n.nw with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.nwStart n.nwEnd, warns.toArray, emptyLevel4⟩
          | some c1 =>
          match macrocellLeafChild leaves isLeaf n.ne with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.neStart n.neEnd, warns.toArray, emptyLevel4⟩
          | some c2 =>
          match macrocellLeafChild leaves isLeaf n.sw with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.swStart n.swEnd, warns.toArray, emptyLevel4⟩
          | some c3 =>
          match macrocellLeafChild leaves isLeaf n.se with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.seStart n.seEnd, warns.toArray, emptyLevel4⟩
          | some c4 =>
            deserializeMacrocell.loop lines numLines (i + 1) false (formatMacrocellNode level a b c d).toByteArray
              (formatMacrocellNode level a b c d).toByteArray.size.toUInt32 0 0 0 0 0
              (nodes.push (makeLevel4Node c1 c2 c3 c4)) (leaves.push 0) (isLeaf.push false) warns
        else
          match macrocellCellChild nodes isLeaf n.level (emptyMacroCellUInt32 (n.level - 1)) n.nw with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.nwStart n.nwEnd, warns.toArray, emptyLevel4⟩
          | some c1 =>
          match macrocellCellChild nodes isLeaf n.level (emptyMacroCellUInt32 (n.level - 1)) n.ne with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.neStart n.neEnd, warns.toArray, emptyLevel4⟩
          | some c2 =>
          match macrocellCellChild nodes isLeaf n.level (emptyMacroCellUInt32 (n.level - 1)) n.sw with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.swStart n.swEnd, warns.toArray, emptyLevel4⟩
          | some c3 =>
          match macrocellCellChild nodes isLeaf n.level (emptyMacroCellUInt32 (n.level - 1)) n.se with
          | none => ⟨.unexpectedNodeId (formatMacrocellNode level a b c d) i n.seStart n.seEnd, warns.toArray, emptyLevel4⟩
          | some c4 =>
            deserializeMacrocell.loop lines numLines (i + 1) false (formatMacrocellNode level a b c d).toByteArray
              (formatMacrocellNode level a b c d).toByteArray.size.toUInt32 0 0 0 0 0
              (nodes.push (makeCellNode c1 c2 c3 c4)) (leaves.push 0) (isLeaf.push false) warns) := by
  obtain ⟨n, hn, h0, h1, h2, h3, h4⟩ := parseMCNodeLine_format level a b c d
  obtain ⟨hpos, hdig, hsz⟩ := formatMacrocellNode_first level a b c d
  refine ⟨n, h0, h1, h2, h3, h4, ?_⟩
  rw [deserializeMacrocell.loop]
  simp only [hi, ↓reduceDIte, Bool.false_eq_true, ite_false, hline]
  have hl0 : ((formatMacrocellNode level a b c d).toByteArray.size.toUInt32 == 0) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt32.toNat_inj, u32_size_toNat hsz, UInt32.toNat_zero]; omega
  have h35 : ((formatMacrocellNode level a b c d).toByteArray.get! 0 == 35) = false := by
    have := (isDigitByte_iff _).mp hdig
    rw [beq_eq_false_iff_ne]; intro h; rw [h] at this; simp at this
  simp only [hl0, h35, hdig, Bool.false_eq_true, ite_false, ite_true, hn]
  rfl

/-- The nodes, leaves and leaf flags that the reader builds from node lines `ls`, all of which are valid. -/
inductive Reads : List String → Array MacroCell → Array UInt64 → Array Bool → Prop
  | nil : Reads [] #[] #[] #[]
  | leaf {ls N Lv IL} (leaf : UInt64) : Reads ls N Lv IL →
      Reads (ls ++ [formatLeafNode leaf]) (N.push (makeLevel4Node leaf 0 0 0)) (Lv.push leaf) (IL.push true)
  | node4 {ls N Lv IL} (a b c d : UInt32) (c1 c2 c3 c4 : UInt64) : Reads ls N Lv IL →
      leafChildA Lv IL a = some c1 → leafChildA Lv IL b = some c2 → leafChildA Lv IL c = some c3 →
      leafChildA Lv IL d = some c4 →
      Reads (ls ++ [formatMacrocellNode 4 a b c d]) (N.push (makeLevel4Node c1 c2 c3 c4)) (Lv.push 0) (IL.push false)
  | nodeN {ls N Lv IL} (L a b c d : UInt32) (c1 c2 c3 c4 : MacroCell) : Reads ls N Lv IL → 5 ≤ L.toNat →
      L.toNat ≤ 63 →
      cellChildA N IL L (emptyMacroCellUInt32 (L - 1)) a = some c1 →
      cellChildA N IL L (emptyMacroCellUInt32 (L - 1)) b = some c2 →
      cellChildA N IL L (emptyMacroCellUInt32 (L - 1)) c = some c3 →
      cellChildA N IL L (emptyMacroCellUInt32 (L - 1)) d = some c4 →
      Reads (ls ++ [formatMacrocellNode L a b c d]) (N.push (makeCellNode c1 c2 c3 c4)) (Lv.push 0) (IL.push false)

theorem Reads.sizes {ls : List String} {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool}
    (h : Reads ls N Lv IL) : N.size = ls.length ∧ Lv.size = ls.length ∧ IL.size = ls.length := by
  induction h with
  | nil => simp
  | leaf _ _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | node4 _ _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | nodeN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih.1, ih.2.1, ih.2.2]

theorem lines_get (lines : Array String) (hdr x : String) (ls more : List String)
    (h : lines.toList = hdr :: (ls ++ x :: more)) : lines[1 + ls.length]! = x := by
  have hk : 1 + ls.length < lines.size := by rw [← Array.length_toList, h]; simp; omega
  rw [getElem!_pos lines _ hk, ← Array.getElem_toList]
  simp only [h, Nat.add_comm 1 ls.length, List.getElem_cons_succ]
  simp

theorem reads_loop {ls : List String} {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool}
    (h : Reads ls N Lv IL) :
    ∀ (lines : Array String) (hdr : String) (more : List String), lines.toList = hdr :: (ls ++ more) →
      lines.size < 2 ^ 31 → ∀ (B0 : ByteArray) (lim0 : UInt32),
      ∃ (nodes : GrowBuf MacroCell) (leaves : GrowBuf UInt64) (isLeaf : GrowBuf Bool) (B : ByteArray) (lim : UInt32),
        nodes.Rep N ∧ leaves.Rep Lv ∧ isLeaf.Rep IL ∧
        deserializeMacrocell.loop lines lines.size.toUInt32 1 false B0 lim0 0 0 0 0 0 GrowBuf.empty GrowBuf.empty
            GrowBuf.empty GrowBuf.empty =
          deserializeMacrocell.loop lines lines.size.toUInt32 (1 + ls.length).toUInt32 false B lim 0 0 0 0 0
            nodes leaves isLeaf GrowBuf.empty := by
  induction h with
  | nil =>
    intro lines hdr more _ _ B0 lim0
    exact ⟨_, _, _, B0, lim0, GrowBuf.rep_empty, GrowBuf.rep_empty, GrowBuf.rep_empty, rfl⟩
  | leaf leaf hr ih =>
    rename_i ls N Lv IL
    intro lines hdr more hl hsz B0 lim0
    have hsizes := hr.sizes
    obtain ⟨nodes, leaves, isLeaf, B, lim, hn, hlv, hil, he⟩ :=
      ih lines hdr ([formatLeafNode leaf] ++ more) (by rw [hl]; simp) hsz B0 lim0
    have hlen : lines.size = ls.length + 1 + 1 + more.length := by rw [← Array.length_toList, hl]; simp; omega
    have hk : (1 + ls.length).toUInt32.toNat = 1 + ls.length := u32_size_toNat (by omega)
    have hi : (1 + ls.length).toUInt32 < lines.size.toUInt32 := by
      rw [u32_lt_size_iff (by omega), hk]; omega
    have hline : lines[(1 + ls.length).toUInt32.toNat]! = formatLeafNode leaf := by
      rw [hk]; exact lines_get lines hdr _ ls more (by rw [hl]; simp)
    rw [he, loop_leafLine lines _ _ hi leaf hline]
    refine ⟨_, _, _, (formatLeafNode leaf).toByteArray, (formatLeafNode leaf).toByteArray.size.toUInt32,
      GrowBuf.rep_push hn _ (by omega), GrowBuf.rep_push hlv _ (by omega),
      GrowBuf.rep_push hil _ (by omega), ?_⟩
    congr 1
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hk, u32_size_toNat (by simp; omega)]; simp; omega
  | node4 a b c d c1 c2 c3 c4 hr h1 h2 h3 h4 ih =>
    rename_i ls N Lv IL
    intro lines hdr more hl hsz B0 lim0
    have hsizes := hr.sizes
    obtain ⟨nodes, leaves, isLeaf, B, lim, hn, hlv, hil, he⟩ :=
      ih lines hdr ([formatMacrocellNode 4 a b c d] ++ more) (by rw [hl]; simp) hsz B0 lim0
    have hlen : lines.size = ls.length + 1 + 1 + more.length := by rw [← Array.length_toList, hl]; simp; omega
    have hk : (1 + ls.length).toUInt32.toNat = 1 + ls.length := u32_size_toNat (by omega)
    have hi : (1 + ls.length).toUInt32 < lines.size.toUInt32 := by
      rw [u32_lt_size_iff (by omega), hk]; omega
    have hline : lines[(1 + ls.length).toUInt32.toNat]! = formatMacrocellNode 4 a b c d := by
      rw [hk]; exact lines_get lines hdr _ ls more (by rw [hl]; simp)
    obtain ⟨n, hn0, hn1, hn2, hn3, hn4, hstep⟩ := loop_nodeLine_prefix lines _ _ hi 4 a b c d hline B lim 0 0 0 0 0
      nodes leaves isLeaf GrowBuf.empty
    rw [he, hstep, hn0, hn1, hn2, hn3, hn4]
    have hsz' : IL.size ≤ Lv.size := by omega
    simp only [show (decide ((4 : UInt32) < 4) || decide ((4 : UInt32) > maxMacrocellLevel)) = false from rfl,
      Bool.false_eq_true, ite_false, show ((4 : UInt32) == 4) = true from rfl, ite_true,
      macrocellLeafChild_eq hlv hil hsz', h1, h2, h3, h4]
    refine ⟨_, _, _, (formatMacrocellNode 4 a b c d).toByteArray,
      (formatMacrocellNode 4 a b c d).toByteArray.size.toUInt32, GrowBuf.rep_push hn _ (by omega), GrowBuf.rep_push hlv _ (by omega),
      GrowBuf.rep_push hil _ (by omega), ?_⟩
    congr 1
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hk, u32_size_toNat (by simp; omega)]; simp; omega
  | nodeN L a b c d c1 c2 c3 c4 hr h5 h63 h1 h2 h3 h4 ih =>
    rename_i ls N Lv IL
    intro lines hdr more hl hsz B0 lim0
    have hsizes := hr.sizes
    obtain ⟨nodes, leaves, isLeaf, B, lim, hn, hlv, hil, he⟩ :=
      ih lines hdr ([formatMacrocellNode L a b c d] ++ more) (by rw [hl]; simp) hsz B0 lim0
    have hlen : lines.size = ls.length + 1 + 1 + more.length := by rw [← Array.length_toList, hl]; simp; omega
    have hk : (1 + ls.length).toUInt32.toNat = 1 + ls.length := u32_size_toNat (by omega)
    have hi : (1 + ls.length).toUInt32 < lines.size.toUInt32 := by
      rw [u32_lt_size_iff (by omega), hk]; omega
    have hline : lines[(1 + ls.length).toUInt32.toNat]! = formatMacrocellNode L a b c d := by
      rw [hk]; exact lines_get lines hdr _ ls more (by rw [hl]; simp)
    obtain ⟨n, hn0, hn1, hn2, hn3, hn4, hstep⟩ := loop_nodeLine_prefix lines _ _ hi L a b c d hline B lim 0 0 0 0 0
      nodes leaves isLeaf GrowBuf.empty
    rw [he, hstep, hn0, hn1, hn2, hn3, hn4]
    have hsz' : IL.size ≤ N.size := by omega
    have hc1 : (decide (L < 4) || decide (L > maxMacrocellLevel)) = false := by
      simp only [maxMacrocellLevel, Bool.or_eq_false_iff, decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt,
        gt_iff_lt]
      simp; omega
    have hc2 : (L == 4) = false := by
      rw [beq_eq_false_iff_ne]; intro h; subst h; simp at h5
    simp only [hc1, hc2, Bool.false_eq_true, ite_false, macrocellCellChild_eq hn hil hsz', h1, h2, h3, h4]
    refine ⟨_, _, _, (formatMacrocellNode L a b c d).toByteArray,
      (formatMacrocellNode L a b c d).toByteArray.size.toUInt32, GrowBuf.rep_push hn _ (by omega), GrowBuf.rep_push hlv _ (by omega),
      GrowBuf.rep_push hil _ (by omega), ?_⟩
    congr 1
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, hk, u32_size_toNat (by simp; omega)]; simp; omega

theorem macroCellAt_rep {nodes : GrowBuf MacroCell} {N : Array MacroCell} (hn : nodes.Rep N) (i : UInt32)
    (hi : i.toNat < N.size) : macroCellAt nodes.data i = macroCellAt N i := by
  unfold macroCellAt
  rw [rep_getElem! hn _ hi]

theorem macrocellHeader_check :
    (macrocellHeader.toByteArray.size.toUInt32 < 4 || macrocellHeader.toByteArray.get! 0 != 91 ||
      macrocellHeader.toByteArray.get! 1 != 77 || macrocellHeader.toByteArray.get! 2 != 50 ||
      macrocellHeader.toByteArray.get! 3 != 93) = false := by decide

/-- The reader returns the last node of valid lines after the header, with no warnings. -/
theorem deserializeMacrocell_reads {ls : List String} {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool}
    (h : Reads ls N Lv IL) (lines : Array String) (hl : lines.toList = macrocellHeader :: ls)
    (hsz : lines.size < 2 ^ 31) (hne : N.size ≠ 0) :
    deserializeMacrocell lines = ⟨.ok, #[], macroCellAt N (N.size - 1).toUInt32⟩ := by
  have hsizes := h.sizes
  have hlen : lines.size = ls.length + 1 := by rw [← Array.length_toList, hl]; simp
  have h0 : lines[0]! = macrocellHeader := by
    rw [getElem!_pos lines 0 (by omega), ← Array.getElem_toList]; simp [hl]
  unfold deserializeMacrocell
  simp only [h0, macrocellHeader_check, Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by rw [beq_iff_eq, ← UInt32.toNat_inj, u32_size_toNat (by omega), UInt32.toNat_zero]; omega)]
  obtain ⟨nodes, leaves, isLeaf, B, lim, hn, hlv, hil, he⟩ :=
    reads_loop h lines macrocellHeader [] (by simp [hl]) hsz macrocellHeader.toByteArray 0
  rw [he, deserializeMacrocell.loop]
  have hnot : ¬ (1 + ls.length).toUInt32 < lines.size.toUInt32 := by
    rw [u32_lt_size_iff (by omega), u32_size_toNat (by omega)]; omega
  have hns : nodes.size.toNat = N.size := hn.1
  have hns0 : (nodes.size == 0) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← UInt32.toNat_inj, hns, UInt32.toNat_zero]; exact hne
  simp only [hnot, ↓reduceDIte, hns0, Bool.false_eq_true, ite_false, GrowBuf.rep_empty.2.2.2]
  have hidx : nodes.size - 1 = (N.size - 1).toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), hns, UInt32.toNat_one,
      u32_size_toNat (by omega)]
  rw [hidx, macroCellAt_rep hn _ (by rw [u32_size_toNat (by omega)]; omega)]

/-! ## The writer -/

/-- A node built with the smart constructors, with children of equal levels. -/
def Canonical : MacroCell → Prop
  | .level4Node h a b c d => h = level4Hash a b c d
  | .cellNode h a b c d => Canonical a ∧ Canonical b ∧ Canonical c ∧ Canonical d ∧ b.depth = a.depth ∧
      c.depth = a.depth ∧ d.depth = a.depth ∧
      h = cellNodeHash (a.level + 1) a.cellHashCode b.cellHashCode c.cellHashCode d.cellHashCode

/-- The reader's arrays grow from `(N, Lv, IL)` to `(N', Lv', IL')`. -/
def Ext (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool) (N' : Array MacroCell) (Lv' : Array UInt64)
    (IL' : Array Bool) : Prop :=
  N.size ≤ N'.size ∧ IL.size ≤ IL'.size ∧ Lv.size ≤ Lv'.size ∧ (∀ k < N.size, N'[k]! = N[k]!) ∧
    (∀ k < IL.size, IL'[k]! = IL[k]!) ∧ (∀ k < Lv.size, Lv'[k]! = Lv[k]!)

theorem Ext.refl (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool) : Ext N Lv IL N Lv IL :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Ext.trans {N₁ N₂ N₃ : Array MacroCell} {Lv₁ Lv₂ Lv₃ : Array UInt64} {IL₁ IL₂ IL₃ : Array Bool}
    (h1 : Ext N₁ Lv₁ IL₁ N₂ Lv₂ IL₂) (h2 : Ext N₂ Lv₂ IL₂ N₃ Lv₃ IL₃) : Ext N₁ Lv₁ IL₁ N₃ Lv₃ IL₃ :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2.1 h2.2.1, Nat.le_trans h1.2.2.1 h2.2.2.1,
    fun k hk => (h2.2.2.2.1 k (by have := h1.1; omega)).trans (h1.2.2.2.1 k hk),
    fun k hk => (h2.2.2.2.2.1 k (by have := h1.2.1; omega)).trans (h1.2.2.2.2.1 k hk),
    fun k hk => (h2.2.2.2.2.2 k (by have := h1.2.2.1; omega)).trans (h1.2.2.2.2.2 k hk)⟩

theorem array_push_getElem! {α : Type} [Inhabited α] (a : Array α) (x : α) (k : Nat) (hk : k < a.size) :
    (a.push x)[k]! = a[k]! := by
  rw [getElem!_pos _ k (by simp; omega), getElem!_pos a k hk, Array.getElem_push_lt hk]

theorem array_push_getElem!_last {α : Type} [Inhabited α] (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

theorem Ext.push (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool) (m : MacroCell) (v : UInt64) (b : Bool) :
    Ext N Lv IL (N.push m) (Lv.push v) (IL.push b) :=
  ⟨by simp, by simp, by simp, fun k hk => array_push_getElem! N m k hk, fun k hk => array_push_getElem! IL b k hk,
    fun k hk => array_push_getElem! Lv v k hk⟩

theorem leafChildA_ext {N N' : Array MacroCell} {Lv Lv' : Array UInt64} {IL IL' : Array Bool}
    (he : Ext N Lv IL N' Lv' IL') (hsz : IL.size ≤ Lv.size) (id : UInt32) (v : UInt64)
    (h : leafChildA Lv IL id = some v) : leafChildA Lv' IL' id = some v := by
  unfold leafChildA at h ⊢
  by_cases h0 : (id == 0) = true
  · simpa [h0] using h
  · simp only [h0, Bool.false_eq_true, ite_false] at h ⊢
    by_cases hgt : id.toNat > IL.size
    · simp [hgt] at h
    · have hid : 1 ≤ id.toNat := by
        have : id ≠ 0 := by simpa using h0
        have : id.toNat ≠ 0 := fun h' => this (UInt32.toNat_inj.mp (by rw [h']; rfl)); omega
      have hsub : (id - 1).toNat = id.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
      simp only [hgt, ite_false] at h
      have hgt' : ¬ id.toNat > IL'.size := by have := he.2.1; omega
      simp only [hgt', ite_false]
      rw [hsub] at h ⊢
      rw [he.2.2.2.2.1 _ (by omega), he.2.2.2.2.2 _ (by omega)]
      exact h

theorem macroCellAt_ext {N N' : Array MacroCell} {Lv Lv' : Array UInt64} {IL IL' : Array Bool}
    (he : Ext N Lv IL N' Lv' IL') (i : UInt32) (hi : i.toNat < N.size) : macroCellAt N' i = macroCellAt N i := by
  unfold macroCellAt; rw [he.2.2.2.1 _ hi]

theorem cellChildA_ext {N N' : Array MacroCell} {Lv Lv' : Array UInt64} {IL IL' : Array Bool}
    (he : Ext N Lv IL N' Lv' IL') (hsz : IL.size ≤ N.size) (L : UInt32) (e : MacroCell) (id : UInt32) (v : MacroCell)
    (h : cellChildA N IL L e id = some v) : cellChildA N' IL' L e id = some v := by
  unfold cellChildA at h ⊢
  by_cases h0 : (id == 0) = true
  · simpa [h0] using h
  · simp only [h0, Bool.false_eq_true, ite_false] at h ⊢
    by_cases hgt : id.toNat > IL.size
    · simp [hgt] at h
    · have hid : 1 ≤ id.toNat := by
        have : id ≠ 0 := by simpa using h0
        have : id.toNat ≠ 0 := fun h' => this (UInt32.toNat_inj.mp (by rw [h']; rfl)); omega
      have hsub : (id - 1).toNat = id.toNat - 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
      simp only [hgt, ite_false] at h
      have hgt' : ¬ id.toNat > IL'.size := by have := he.2.1; omega
      simp only [hgt', ite_false]
      rw [he.2.2.2.2.1 _ (by rw [hsub]; omega), macroCellAt_ext he _ (by rw [hsub]; omega)]
      exact h

/-- The node that a node line with `key` (level and children's numbers) reads as. -/
def KeyDenotes (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool)
    (key : UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (m : MacroCell) : Prop :=
  (key.1 = 4 ∧ ∃ c1 c2 c3 c4, leafChildA Lv IL key.2.1 = some c1 ∧ leafChildA Lv IL key.2.2.1 = some c2 ∧
    leafChildA Lv IL key.2.2.2.1 = some c3 ∧ leafChildA Lv IL key.2.2.2.2 = some c4 ∧
    m = makeLevel4Node c1 c2 c3 c4) ∨
  (5 ≤ key.1.toNat ∧ key.1.toNat ≤ 63 ∧ ∃ m1 m2 m3 m4,
    cellChildA N IL key.1 (emptyMacroCellUInt32 (key.1 - 1)) key.2.1 = some m1 ∧
    cellChildA N IL key.1 (emptyMacroCellUInt32 (key.1 - 1)) key.2.2.1 = some m2 ∧
    cellChildA N IL key.1 (emptyMacroCellUInt32 (key.1 - 1)) key.2.2.2.1 = some m3 ∧
    cellChildA N IL key.1 (emptyMacroCellUInt32 (key.1 - 1)) key.2.2.2.2 = some m4 ∧
    m = makeCellNode m1 m2 m3 m4)

theorem KeyDenotes_ext {N N' : Array MacroCell} {Lv Lv' : Array UInt64} {IL IL' : Array Bool}
    (he : Ext N Lv IL N' Lv' IL') (hsz1 : IL.size ≤ Lv.size) (hsz2 : IL.size ≤ N.size) {key m}
    (h : KeyDenotes N Lv IL key m) : KeyDenotes N' Lv' IL' key m := by
  rcases h with ⟨h4, c1, c2, c3, c4, h1, h2, h3, h4', rfl⟩ | ⟨h5, h63, m1, m2, m3, m4, h1, h2, h3, h4, rfl⟩
  · exact Or.inl ⟨h4, c1, c2, c3, c4, leafChildA_ext he hsz1 _ _ h1, leafChildA_ext he hsz1 _ _ h2,
      leafChildA_ext he hsz1 _ _ h3, leafChildA_ext he hsz1 _ _ h4', rfl⟩
  · exact Or.inr ⟨h5, h63, m1, m2, m3, m4, cellChildA_ext he hsz2 _ _ _ _ h1, cellChildA_ext he hsz2 _ _ _ _ h2,
      cellChildA_ext he hsz2 _ _ _ _ h3, cellChildA_ext he hsz2 _ _ _ _ h4, rfl⟩

theorem KeyDenotes_unique {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool} {key m m'}
    (h : KeyDenotes N Lv IL key m) (h' : KeyDenotes N Lv IL key m') : m = m' := by
  rcases h with ⟨h4, c1, c2, c3, c4, h1, h2, h3, h4', rfl⟩ | ⟨h5, h63, m1, m2, m3, m4, h1, h2, h3, h4, rfl⟩ <;>
    rcases h' with ⟨g4, d1, d2, d3, d4, g1, g2, g3, g4', rfl⟩ | ⟨g5, g63, n1, n2, n3, n4, g1, g2, g3, g4, rfl⟩
  · rw [h1] at g1; rw [h2] at g2; rw [h3] at g3; rw [h4'] at g4'
    simp only [Option.some.injEq] at g1 g2 g3 g4'; subst g1 g2 g3 g4'; rfl
  · rw [h4] at g5; simp at g5
  · rw [g4] at h5; simp at h5
  · rw [h1] at g1; rw [h2] at g2; rw [h3] at g3; rw [h4] at g4
    simp only [Option.some.injEq] at g1 g2 g3 g4; subst g1 g2 g3 g4; rfl

/-- The writer state `st` matches the reader's arrays: its lines read as them, and its memos name nodes in them. -/
def Inv (st : MacrocellWriterState) (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool) : Prop :=
  ∃ ls, st.lines = macrocellHeader :: ls ∧ Reads ls N Lv IL ∧ st.lines.length < 2 ^ 31 ∧
    (∀ p ∈ st.leaves, p.1 ≠ 0 ∧ leafChildA Lv IL p.2 = some p.1) ∧
    (∀ p ∈ st.nodes, p.2 ≠ 0 ∧ ∃ m, KeyDenotes N Lv IL p.1 m ∧
      cellChildA N IL (p.1.1 + 1) (emptyMacroCellUInt32 p.1.1) p.2 = some m)

theorem Inv.ext {st : MacrocellWriterState} {N N' : Array MacroCell} {Lv Lv' : Array UInt64} {IL IL' : Array Bool}
    (h : Inv st N Lv IL) (he : Ext N Lv IL N' Lv' IL') :
    (∀ p ∈ st.leaves, leafChildA Lv' IL' p.2 = some p.1) ∧
      (∀ p ∈ st.nodes, p.2 ≠ 0 ∧ ∃ m, KeyDenotes N' Lv' IL' p.1 m ∧
        cellChildA N' IL' (p.1.1 + 1) (emptyMacroCellUInt32 p.1.1) p.2 = some m) := by
  obtain ⟨ls, -, hr, -, hlv, hnd⟩ := h
  have hs := hr.sizes
  refine ⟨fun p hp => leafChildA_ext he (by omega) _ _ (hlv p hp).2, fun p hp => ?_⟩
  obtain ⟨h0, m, hk, hc⟩ := hnd p hp
  exact ⟨h0, m, KeyDenotes_ext he (by omega) (by omega) hk, cellChildA_ext he (by omega) _ _ _ _ hc⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] (a : α) (b : β) :
    ∀ (l : List (α × β)), l.lookup a = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => simp [List.lookup]
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    intro h
    simp only [List.lookup] at h
    by_cases ha : (a == a') = true
    · rw [ha] at h; simp only [Option.some.injEq] at h; subst h
      rw [beq_iff_eq] at ha; subst ha; simp
    · simp only [ha] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem nextId_eq (st : MacrocellWriterState) (ls : List String) (h : st.lines = macrocellHeader :: ls)
    (hl : st.lines.length < 2 ^ 31) : st.nextId.toNat = ls.length + 1 := by
  unfold MacrocellWriterState.nextId
  rw [h, u32_size_toNat (by rw [h] at hl; simpa using (by omega : (macrocellHeader :: ls).length < 2 ^ 32))]
  simp

theorem leafChildA_new (Lv : Array UInt64) (IL : Array Bool) (hsz : IL.size = Lv.size) (v : UInt64) (id : UInt32)
    (hid : id.toNat = IL.size + 1) : leafChildA (Lv.push v) (IL.push true) id = some v := by
  unfold leafChildA
  have h0 : (id == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h; subst h; simp at hid
  have hsub : (id - 1).toNat = IL.size := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]; omega
  simp only [h0, Bool.false_eq_true, ite_false, Array.size_push, hsub]
  rw [ite_eq_right (by omega), array_push_getElem!_last, hsz, array_push_getElem!_last]
  simp

/-- `addLeaf` keeps the invariant, and the leaf's number reads back as the leaf. -/
theorem addLeaf_spec (st : MacrocellWriterState) (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool)
    (h : Inv st N Lv IL) (leaf : UInt64) (hlen : (st.addLeaf leaf).2.lines.length < 2 ^ 31) :
    ∃ N' Lv' IL', Inv (st.addLeaf leaf).2 N' Lv' IL' ∧ Ext N Lv IL N' Lv' IL' ∧
      leafChildA Lv' IL' (st.addLeaf leaf).1 = some leaf ∧ (st.addLeaf leaf).2.nodes = st.nodes := by
  unfold MacrocellWriterState.addLeaf at hlen ⊢
  by_cases h0 : (leaf == 0) = true
  · simp only [h0, ite_true] at hlen ⊢
    refine ⟨N, Lv, IL, h, Ext.refl _ _ _, ?_, trivial⟩
    rw [beq_iff_eq] at h0; subst h0; simp [leafChildA]
  · simp only [h0, Bool.false_eq_true, ite_false] at hlen ⊢
    cases hl : st.leaves.lookup leaf with
    | some id =>
      simp only [hl] at hlen ⊢
      exact ⟨N, Lv, IL, h, Ext.refl _ _ _, (h.choose_spec.2.2.2.1 _ (lookup_mem leaf id _ hl)).2, trivial⟩
    | none =>
      simp only [hl] at hlen ⊢
      obtain ⟨ls, hls, hr, hll, hlv, hnd⟩ := h
      have hs := hr.sizes
      have hid := nextId_eq st ls hls hll
      have he := Ext.push N Lv IL (makeLevel4Node leaf 0 0 0) leaf true
      obtain ⟨hlv', hnd'⟩ := Inv.ext ⟨ls, hls, hr, hll, hlv, hnd⟩ he
      refine ⟨_, _, _, ⟨ls ++ [formatLeafNode leaf], by simp [hls], Reads.leaf leaf hr, hlen, ?_, hnd'⟩, he,
        leafChildA_new Lv IL (by omega) leaf _ (by omega), trivial⟩
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨by simpa using h0, leafChildA_new Lv IL (by omega) leaf _ (by simp only; omega)⟩
      · exact ⟨(hlv p hp).1, hlv' p hp⟩

theorem emptyMacroCellUInt32_level (L : UInt32) (h4 : 4 ≤ L.toNat) (h63 : L.toNat ≤ 63) :
    (emptyMacroCellUInt32 L).level = L := by
  obtain ⟨-, hd⟩ := emptyMacroCellUInt32_ok L h4 h63
  apply UInt32.toNat_inj.mp
  rw [level_toNat_eq_depth _ (by omega), hd]

theorem cellChildA_level {N : Array MacroCell} {IL : Array Bool} {L : UInt32} (h5 : 5 ≤ L.toNat) (h63 : L.toNat ≤ 63)
    {id : UInt32} {v : MacroCell} (h : cellChildA N IL L (emptyMacroCellUInt32 (L - 1)) id = some v) :
    v.level + 1 = L := by
  have hL1 : (L - 1).toNat = L.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]
  unfold cellChildA at h
  by_cases h0 : (id == 0) = true
  · simp only [h0, ite_true, Option.some.injEq] at h
    subst h
    rw [emptyMacroCellUInt32_level _ (by omega) (by omega)]
    simp
  · simp only [h0, Bool.false_eq_true, ite_false] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i hl; simp only [Option.some.injEq] at h; subst h; simpa using hl
        · simp at h

theorem MacroCell.level_makeCellNode (a b c d : MacroCell) : (makeCellNode a b c d).level = a.level + 1 := rfl

theorem KeyDenotes_level {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool} {key m}
    (h : KeyDenotes N Lv IL key m) : m.level = key.1 := by
  rcases h with ⟨h4, -, -, -, -, -, -, -, -, rfl⟩ | ⟨h5, h63, m1, -, -, -, h1, -, -, -, rfl⟩
  · rw [h4]; rfl
  · rw [MacroCell.level_makeCellNode]; exact cellChildA_level h5 h63 h1

theorem KeyDenotes_made {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool} {key m}
    (h : KeyDenotes N Lv IL key m) :
    (∃ c1 c2 c3 c4, m = makeLevel4Node c1 c2 c3 c4) ∨ (∃ m1 m2 m3 m4, m = makeCellNode m1 m2 m3 m4) := by
  rcases h with ⟨-, c1, c2, c3, c4, -, -, -, -, rfl⟩ | ⟨-, -, m1, m2, m3, m4, -, -, -, -, rfl⟩
  · exact Or.inl ⟨c1, c2, c3, c4, rfl⟩
  · exact Or.inr ⟨m1, m2, m3, m4, rfl⟩

theorem macroCellAt_made (N : Array MacroCell) (k : UInt32)
    (h : (∃ c1 c2 c3 c4, N[k.toNat]! = makeLevel4Node c1 c2 c3 c4) ∨
      (∃ m1 m2 m3 m4, N[k.toNat]! = makeCellNode m1 m2 m3 m4)) : macroCellAt N k = N[k.toNat]! := by
  unfold macroCellAt
  rcases h with ⟨c1, c2, c3, c4, he⟩ | ⟨m1, m2, m3, m4, he⟩ <;> rw [he] <;> rfl

theorem cellChildA_new (N : Array MacroCell) (IL : Array Bool) (hsz : IL.size = N.size) (m : MacroCell)
    (hm : (∃ c1 c2 c3 c4, m = makeLevel4Node c1 c2 c3 c4) ∨ (∃ m1 m2 m3 m4, m = makeCellNode m1 m2 m3 m4))
    (L : UInt32) (hL : m.level = L) (e : MacroCell) (id : UInt32) (hid : id.toNat = IL.size + 1) :
    cellChildA (N.push m) (IL.push false) (L + 1) e id = some m := by
  unfold cellChildA
  have h0 : (id == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro h; subst h; simp at hid
  have hsub : (id - 1).toNat = IL.size := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega)), UInt32.toNat_one]; omega
  have hat : macroCellAt (N.push m) (id - 1) = m := by
    rw [macroCellAt_made _ _ (by rw [hsub, hsz, array_push_getElem!_last]; exact hm),
      hsub, hsz, array_push_getElem!_last]
  simp only [h0, Bool.false_eq_true, ite_false, Array.size_push, hsub]
  rw [ite_eq_right (by omega), array_push_getElem!_last]
  simp [hat, hL]

theorem Reads.ofKey {ls : List String} {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool}
    (hr : Reads ls N Lv IL) (L a b c d : UInt32) (m : MacroCell) (hk : KeyDenotes N Lv IL (L, a, b, c, d) m) :
    Reads (ls ++ [formatMacrocellNode L a b c d]) (N.push m) (Lv.push 0) (IL.push false) := by
  rcases hk with ⟨h4, c1, c2, c3, c4, h1, h2, h3, h4', rfl⟩ | ⟨h5, h63, m1, m2, m3, m4, h1, h2, h3, h4, rfl⟩
  · simp only at h4; subst h4
    exact Reads.node4 a b c d c1 c2 c3 c4 hr h1 h2 h3 h4'
  · exact Reads.nodeN L a b c d m1 m2 m3 m4 hr h5 h63 h1 h2 h3 h4

/-- `addNode` keeps the invariant, and the node's number reads back as the node its key denotes. -/
theorem addNode_spec (st : MacrocellWriterState) (N : Array MacroCell) (Lv : Array UInt64) (IL : Array Bool)
    (h : Inv st N Lv IL) (L a b c d : UInt32) (m : MacroCell) (hk : KeyDenotes N Lv IL (L, a, b, c, d) m)
    (hlen : (st.addNode L a b c d).2.lines.length < 2 ^ 31) :
    ∃ N' Lv' IL', Inv (st.addNode L a b c d).2 N' Lv' IL' ∧ Ext N Lv IL N' Lv' IL' ∧
      cellChildA N' IL' (L + 1) (emptyMacroCellUInt32 L) (st.addNode L a b c d).1 = some m ∧
      (st.addNode L a b c d).2.leaves = st.leaves ∧
      (∀ p ∈ (st.addNode L a b c d).2.nodes, p ∈ st.nodes ∨ p.1.1 = L) ∧
      (st.nodes.lookup (L, a, b, c, d) = none → N' = N.push m ∧ (st.addNode L a b c d).1.toNat = N'.size) := by
  unfold MacrocellWriterState.addNode at hlen ⊢
  cases hl : st.nodes.lookup (L, a, b, c, d) with
  | some id =>
    simp only [hl] at hlen ⊢
    obtain ⟨-, m', hk', hc⟩ := h.choose_spec.2.2.2.2 _ (lookup_mem _ id _ hl)
    have := KeyDenotes_unique hk hk'
    subst this
    exact ⟨N, Lv, IL, h, Ext.refl _ _ _, hc, trivial, fun p hp => Or.inl hp, fun h => by simp at h⟩
  | none =>
    simp only [hl] at hlen ⊢
    obtain ⟨ls, hls, hr, hll, hlv, hnd⟩ := h
    have hs := hr.sizes
    have hid := nextId_eq st ls hls hll
    have he := Ext.push N Lv IL m 0 false
    obtain ⟨hlv', hnd'⟩ := Inv.ext ⟨ls, hls, hr, hll, hlv, hnd⟩ he
    have hnew := cellChildA_new N IL (by omega) m (KeyDenotes_made hk) L (KeyDenotes_level hk)
      (emptyMacroCellUInt32 L) st.nextId (by omega)
    refine ⟨_, _, _, ⟨ls ++ [formatMacrocellNode L a b c d], by simp [hls], hr.ofKey L a b c d m hk, hlen,
      fun p hp => ⟨(hlv p hp).1, hlv' p hp⟩, ?_⟩, he, hnew, trivial, ?_, fun _ => ⟨rfl, by simp; omega⟩⟩
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨fun h0 => ?_, m, KeyDenotes_ext he (by omega) (by omega) hk, hnew⟩
        have := congrArg UInt32.toNat h0; simp only [UInt32.toNat_zero] at this; omega
      · exact hnd' p hp
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inr rfl
      · exact Or.inl hp

theorem depth_ge_four : ∀ m : MacroCell, 4 ≤ m.depth
  | .level4Node .. => by simp [MacroCell.depth]
  | .cellNode _ nw _ _ _ => by have := depth_ge_four nw; simp [MacroCell.depth]; omega

/-- `n` levels of nodes of four equal children over `x`. -/
def mkIter : Nat → MacroCell → MacroCell
  | 0, x => x
  | n + 1, x => mkIter n (makeCellNode x x x x)

theorem mkIter_succ' : ∀ (n : Nat) (x : MacroCell),
    mkIter (n + 1) x = makeCellNode (mkIter n x) (mkIter n x) (mkIter n x) (mkIter n x)
  | 0, _ => rfl
  | n + 1, x => by rw [mkIter, mkIter_succ' n, mkIter]

theorem emptyMacroCellUInt32_loop_iter (L : UInt32) :
    ∀ (n : Nat) (cur : UInt32) (node : MacroCell), L.toNat - cur.toNat = n → cur.toNat ≤ L.toNat →
      emptyMacroCellUInt32.loop L cur node = mkIter n node := by
  intro n
  induction n with
  | zero =>
    intro cur node hn hle
    rw [emptyMacroCellUInt32.loop, dite_eq_right_iff.mpr (fun h => absurd (UInt32.lt_iff_toNat_lt.mp h) (by omega))]
    rfl
  | succ n ih =>
    intro cur node hn hle
    have hlt : cur < L := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hsucc : (cur + 1).toNat = cur.toNat + 1 := by
      rw [UInt32.toNat_add]; have := UInt32.toNat_lt L; simp; omega
    rw [emptyMacroCellUInt32.loop, dite_eq_left_of_eq_true (by simp [hlt]), ih _ _ (by omega) (by omega), mkIter]

theorem emptyMacroCellUInt32_iter (L : UInt32) (h4 : 4 ≤ L.toNat) :
    emptyMacroCellUInt32 L = mkIter (L.toNat - 4) emptyLevel4 := by
  unfold emptyMacroCellUInt32
  exact emptyMacroCellUInt32_loop_iter L _ 4 emptyLevel4 rfl h4

theorem emptyMacroCellUInt32_succ (L : UInt32) (h4 : 4 ≤ L.toNat) (h63 : L.toNat < 63) :
    emptyMacroCellUInt32 (L + 1) =
      makeCellNode (emptyMacroCellUInt32 L) (emptyMacroCellUInt32 L) (emptyMacroCellUInt32 L)
        (emptyMacroCellUInt32 L) := by
  have h1 : (L + 1).toNat = L.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  rw [emptyMacroCellUInt32_iter _ (by omega), emptyMacroCellUInt32_iter _ h4, h1,
    show L.toNat + 1 - 4 = (L.toNat - 4) + 1 by omega, mkIter_succ']

theorem emptyMacroCellUInt32_four : emptyMacroCellUInt32 4 = emptyLevel4 := by
  rw [emptyMacroCellUInt32_iter _ (by decide)]; rfl

theorem lookup_none {α β : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : List (α × β)), (∀ p ∈ l, p.1 ≠ a) → l.lookup a = none := by
  intro l
  induction l with
  | nil => simp [List.lookup]
  | cons p l ih =>
    obtain ⟨a', b'⟩ := p
    intro h
    simp only [List.lookup]
    have : (a == a') = false := by
      rw [beq_eq_false_iff_ne]; intro he; exact h (a', b') (by simp) he.symm
    rw [this]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem addLeaf_lines (st : MacrocellWriterState) (leaf : UInt64) :
    st.lines.length ≤ (st.addLeaf leaf).2.lines.length := by
  unfold MacrocellWriterState.addLeaf
  split
  · exact Nat.le_refl _
  · split <;> simp

theorem addNode_lines (st : MacrocellWriterState) (L a b c d : UInt32) :
    st.lines.length ≤ (st.addNode L a b c d).2.lines.length := by
  unfold MacrocellWriterState.addNode
  split <;> simp

theorem addTree_lines : ∀ (m : MacroCell) (st : MacrocellWriterState),
    st.lines.length ≤ (st.addTree m).2.lines.length
  | .level4Node h nw ne sw se, st => by
    unfold MacrocellWriterState.addTree
    split
    · exact Nat.le_refl _
    · simp only
      have := addLeaf_lines st nw
      have := addLeaf_lines (st.addLeaf nw).2 ne
      have := addLeaf_lines ((st.addLeaf nw).2.addLeaf ne).2 sw
      have := addLeaf_lines (((st.addLeaf nw).2.addLeaf ne).2.addLeaf sw).2 se
      have := addNode_lines ((((st.addLeaf nw).2.addLeaf ne).2.addLeaf sw).2.addLeaf se).2 4
        (st.addLeaf nw).1 ((st.addLeaf nw).2.addLeaf ne).1 (((st.addLeaf nw).2.addLeaf ne).2.addLeaf sw).1
        ((((st.addLeaf nw).2.addLeaf ne).2.addLeaf sw).2.addLeaf se).1
      omega
  | .cellNode h nw ne sw se, st => by
    unfold MacrocellWriterState.addTree
    simp only
    have h1 := addTree_lines nw st
    have h2 := addTree_lines ne (st.addTree nw).2
    have h3 := addTree_lines sw ((st.addTree nw).2.addTree ne).2
    have h4 := addTree_lines se (((st.addTree nw).2.addTree ne).2.addTree sw).2
    split
    · show _ ≤ ((((st.addTree nw).2.addTree ne).2.addTree sw).2.addTree se).2.lines.length
      omega
    · have := addNode_lines ((((st.addTree nw).2.addTree ne).2.addTree sw).2.addTree se).2 (nw.level + 1)
        (st.addTree nw).1 ((st.addTree nw).2.addTree ne).1 (((st.addTree nw).2.addTree ne).2.addTree sw).1
        ((((st.addTree nw).2.addTree ne).2.addTree sw).2.addTree se).1
      omega

theorem Inv.sizes {st : MacrocellWriterState} {N : Array MacroCell} {Lv : Array UInt64} {IL : Array Bool}
    (h : Inv st N Lv IL) : IL.size = N.size ∧ Lv.size = N.size := by
  obtain ⟨ls, -, hr, -⟩ := h
  have := hr.sizes; omega

theorem Canonical.level4 {h : UInt32} {a b c d : UInt64} (hc : Canonical (.level4Node h a b c d)) :
    MacroCell.level4Node h a b c d = makeLevel4Node a b c d := by
  simp only [Canonical] at hc; subst hc; rfl

theorem Canonical.cell {h : UInt32} {a b c d : MacroCell} (hc : Canonical (.cellNode h a b c d)) :
    MacroCell.cellNode h a b c d = makeCellNode a b c d := by
  obtain ⟨-, -, -, -, -, -, -, hh⟩ := hc; subst hh; rfl

theorem level_lt (m : MacroCell) (hd : m.depth ≤ 63) : m.level.toNat = m.depth ∧ 4 ≤ m.level.toNat := by
  have := level_toNat_eq_depth m (by omega); have := depth_ge_four m; omega

theorem last_of_push (N : Array MacroCell) (m : MacroCell)
    (hm : (∃ c1 c2 c3 c4, m = makeLevel4Node c1 c2 c3 c4) ∨ (∃ m1 m2 m3 m4, m = makeCellNode m1 m2 m3 m4))
    (hN : N.size + 1 < 2 ^ 32) :
    (N.push m).size ≠ 0 ∧ macroCellAt (N.push m) ((N.push m).size - 1).toUInt32 = m := by
  refine ⟨by simp, ?_⟩
  have hk : ((N.push m).size - 1).toUInt32.toNat = N.size := by simp; omega
  rw [macroCellAt_made _ _ (by rw [hk, array_push_getElem!_last]; exact hm), hk, array_push_getElem!_last]

/-- `addTree` keeps the invariant, and the tree's number reads back as the tree. -/
theorem addTree_spec : ∀ (m : MacroCell) (st : MacrocellWriterState) (N : Array MacroCell) (Lv : Array UInt64)
    (IL : Array Bool), Inv st N Lv IL → Canonical m → m.depth ≤ 63 → (st.addTree m).2.lines.length < 2 ^ 31 →
    ∃ N' Lv' IL', Inv (st.addTree m).2 N' Lv' IL' ∧ Ext N Lv IL N' Lv' IL' ∧
      cellChildA N' IL' (m.level + 1) (emptyMacroCellUInt32 m.level) (st.addTree m).1 = some m ∧
      (∀ p ∈ (st.addTree m).2.nodes, p ∈ st.nodes ∨ p.1.1.toNat ≤ m.level.toNat) ∧
      ((∀ p ∈ st.nodes, p.1.1.toNat < m.level.toNat) → (st.addTree m).1 ≠ 0 →
        N'.size ≠ 0 ∧ macroCellAt N' (N'.size - 1).toUInt32 = m)
  | .level4Node h nw ne sw se, st, N, Lv, IL, hinv, hcan, hd, hlen => by
    have hm := hcan.level4
    unfold MacrocellWriterState.addTree at hlen ⊢
    by_cases hz : (nw == 0 && ne == 0 && sw == 0 && se == 0) = true
    · simp only [hz, ite_true] at hlen ⊢
      refine ⟨N, Lv, IL, hinv, Ext.refl _ _ _, ?_, fun p hp => Or.inl hp, fun _ h0 => absurd rfl h0⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hz
      rw [hm]
      show cellChildA N IL (4 + 1) (emptyMacroCellUInt32 4) 0 = some emptyLevel4
      rw [emptyMacroCellUInt32_four]; simp [cellChildA]
    · simp only [hz, Bool.false_eq_true, ite_false] at hlen ⊢
      generalize hs1 : st.addLeaf nw = s1 at hlen ⊢
      generalize hs2 : s1.2.addLeaf ne = s2 at hlen ⊢
      generalize hs3 : s2.2.addLeaf sw = s3 at hlen ⊢
      generalize hs4 : s3.2.addLeaf se = s4 at hlen ⊢
      have l5 := addNode_lines s4.2 4 s1.1 s2.1 s3.1 s4.1
      have l4 := hs4 ▸ addLeaf_lines s3.2 se
      have l3 := hs3 ▸ addLeaf_lines s2.2 sw
      have l2 := hs2 ▸ addLeaf_lines s1.2 ne
      obtain ⟨N1, Lv1, IL1, hi1, he1, hc1, hn1⟩ := addLeaf_spec st N Lv IL hinv nw (by rw [hs1]; omega)
      rw [hs1] at hi1 hc1 hn1
      obtain ⟨N2, Lv2, IL2, hi2, he2, hc2, hn2⟩ := addLeaf_spec s1.2 N1 Lv1 IL1 hi1 ne (by rw [hs2]; omega)
      rw [hs2] at hi2 hc2 hn2
      obtain ⟨N3, Lv3, IL3, hi3, he3, hc3, hn3⟩ := addLeaf_spec s2.2 N2 Lv2 IL2 hi2 sw (by rw [hs3]; omega)
      rw [hs3] at hi3 hc3 hn3
      obtain ⟨N4, Lv4, IL4, hi4, he4, hc4, hn4⟩ := addLeaf_spec s3.2 N3 Lv3 IL3 hi3 se (by rw [hs4]; omega)
      rw [hs4] at hi4 hc4 hn4
      have z1 := hinv.sizes; have z2 := hi1.sizes; have z3 := hi2.sizes; have z4 := hi3.sizes
      have e24 := he2.trans (he3.trans he4)
      have e34 := he3.trans he4
      have hk : KeyDenotes N4 Lv4 IL4 (4, s1.1, s2.1, s3.1, s4.1) (makeLevel4Node nw ne sw se) :=
        Or.inl ⟨rfl, nw, ne, sw, se, leafChildA_ext e24 (by omega) _ _ hc1, leafChildA_ext e34 (by omega) _ _ hc2,
          leafChildA_ext he4 (by omega) _ _ hc3, hc4, rfl⟩
      obtain ⟨N5, Lv5, IL5, hi5, he5, hc5, -, hnodes5, hlast5⟩ := addNode_spec s4.2 N4 Lv4 IL4 hi4 4 _ _ _ _ _ hk hlen
      have hst : s4.2.nodes = st.nodes := by rw [hn4, hn3, hn2, hn1]
      refine ⟨N5, Lv5, IL5, hi5, he1.trans (e24.trans he5), ?_, ?_, ?_⟩
      · rw [hm]; exact hc5
      · intro p hp
        rcases hnodes5 p hp with hp | hp
        · exact Or.inl (hst ▸ hp)
        · exact Or.inr (by rw [hp]; show (4 : UInt32).toNat ≤ 4; simp)
      · intro hlow _
        have hnone : s4.2.nodes.lookup (4, s1.1, s2.1, s3.1, s4.1) = none := by
          apply lookup_none
          intro p hp heq
          have := hlow p (hst ▸ hp)
          rw [heq] at this
          exact absurd this (by show ¬ (4 : UInt32).toNat < 4; simp)
        obtain ⟨rfl, -⟩ := hlast5 hnone
        rw [hm]
        exact last_of_push N4 _ (Or.inl ⟨_, _, _, _, rfl⟩) (by
          obtain ⟨ls, hls, hr, hll, -⟩ := hi4
          have := hr.sizes; have : s4.2.lines.length = ls.length + 1 := by rw [hls]; simp
          omega)
  | .cellNode h nw ne sw se, st, N, Lv, IL, hinv, hcan, hd, hlen => by
    have hm := hcan.cell
    obtain ⟨cnw, cne, csw, cse, hl2, hl3, hl4, -⟩ := hcan
    have hdm : (MacroCell.cellNode h nw ne sw se).depth = nw.depth + 1 := rfl
    have hlvm : (MacroCell.cellNode h nw ne sw se).level = nw.level + 1 := rfl
    obtain ⟨q1, q1'⟩ := level_lt nw (by omega)
    obtain ⟨q2, -⟩ := level_lt ne (by omega)
    obtain ⟨q3, -⟩ := level_lt sw (by omega)
    obtain ⟨q4, -⟩ := level_lt se (by omega)
    have hl2' : ne.level = nw.level := UInt32.toNat_inj.mp (by omega)
    have hl3' : sw.level = nw.level := UInt32.toNat_inj.mp (by omega)
    have hl4' : se.level = nw.level := UInt32.toNat_inj.mp (by omega)
    have hlvn : (nw.level + 1).toNat = nw.level.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
    unfold MacrocellWriterState.addTree at hlen ⊢
    simp only at hlen ⊢
    generalize hs1 : st.addTree nw = s1 at hlen ⊢
    generalize hs2 : s1.2.addTree ne = s2 at hlen ⊢
    generalize hs3 : s2.2.addTree sw = s3 at hlen ⊢
    generalize hs4 : s3.2.addTree se = s4 at hlen ⊢
    have l4 := hs4 ▸ addTree_lines se s3.2
    have l3 := hs3 ▸ addTree_lines sw s2.2
    have l2 := hs2 ▸ addTree_lines ne s1.2
    have l5 : s4.2.lines.length < 2 ^ 31 := by
      split at hlen
      · exact hlen
      · have := addNode_lines s4.2 (nw.level + 1) s1.1 s2.1 s3.1 s4.1; omega
    obtain ⟨N1, Lv1, IL1, hi1, he1, hc1, hn1, -⟩ := addTree_spec nw st N Lv IL hinv cnw (by omega)
      (by rw [hs1]; omega)
    rw [hs1] at hi1 hc1 hn1
    obtain ⟨N2, Lv2, IL2, hi2, he2, hc2, hn2, -⟩ := addTree_spec ne s1.2 N1 Lv1 IL1 hi1 cne (by omega)
      (by rw [hs2]; omega)
    rw [hs2] at hi2 hc2 hn2
    obtain ⟨N3, Lv3, IL3, hi3, he3, hc3, hn3, -⟩ := addTree_spec sw s2.2 N2 Lv2 IL2 hi2 csw (by omega)
      (by rw [hs3]; omega)
    rw [hs3] at hi3 hc3 hn3
    obtain ⟨N4, Lv4, IL4, hi4, he4, hc4, hn4, -⟩ := addTree_spec se s3.2 N3 Lv3 IL3 hi3 cse (by omega)
      (by rw [hs4]; omega)
    rw [hs4] at hi4 hc4 hn4
    rw [hl2'] at hc2; rw [hl3'] at hc3; rw [hl4'] at hc4
    have z1 := hinv.sizes; have z2 := hi1.sizes; have z3 := hi2.sizes; have z4 := hi3.sizes
    have e24 := he2.trans (he3.trans he4)
    have e34 := he3.trans he4
    have g1 := cellChildA_ext e24 (by omega) _ _ _ _ hc1
    have g2 := cellChildA_ext e34 (by omega) _ _ _ _ hc2
    have g3 := cellChildA_ext he4 (by omega) _ _ _ _ hc3
    have hst : ∀ p ∈ s4.2.nodes, p ∈ st.nodes ∨ p.1.1.toNat ≤ nw.level.toNat := by
      intro p hp
      rcases hn4 p hp with hp | hp
      · rcases hn3 p hp with hp | hp
        · rcases hn2 p hp with hp | hp
          · rcases hn1 p hp with hp | hp
            · exact Or.inl hp
            · exact Or.inr hp
          · exact Or.inr (by rw [hl2'] at hp; exact hp)
        · exact Or.inr (by rw [hl3'] at hp; exact hp)
      · exact Or.inr (by rw [hl4'] at hp; exact hp)
    by_cases hz : (s1.1 == 0 && s2.1 == 0 && s3.1 == 0 && s4.1 == 0) = true
    · simp only [hz, ite_true]
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨⟨z1', z2'⟩, z3'⟩, z4'⟩ := hz
      rw [z1'] at g1; rw [z2'] at g2; rw [z3'] at g3; rw [z4'] at hc4
      simp only [cellChildA, beq_self_eq_true, ite_true, Option.some.injEq] at g1 g2 g3 hc4
      refine ⟨N4, Lv4, IL4, hi4, he1.trans e24, ?_, fun p hp => ?_, fun _ h0 => absurd rfl h0⟩
      · rw [hm, ← g1, ← g2, ← g3, ← hc4, ← emptyMacroCellUInt32_succ _ q1' (by omega),
          emptyMacroCellUInt32_level (nw.level + 1) (by omega) (by omega)]
        simp [cellChildA]
      · rcases hst p hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (by rw [hlvm, hlvn]; omega)
    · simp only [hz, Bool.false_eq_true, ite_false] at hlen ⊢
      have hk : KeyDenotes N4 Lv4 IL4 (nw.level + 1, s1.1, s2.1, s3.1, s4.1) (makeCellNode nw ne sw se) := by
        refine Or.inr ⟨by simp only; omega, by simp only; omega, nw, ne, sw, se, ?_⟩
        simp only [UInt32.add_sub_cancel]
        exact ⟨g1, g2, g3, hc4, trivial⟩
      obtain ⟨N5, Lv5, IL5, hi5, he5, hc5, -, hnodes5, hlast5⟩ :=
        addNode_spec s4.2 N4 Lv4 IL4 hi4 _ _ _ _ _ _ hk hlen
      refine ⟨N5, Lv5, IL5, hi5, he1.trans (e24.trans he5), ?_, ?_, ?_⟩
      · rw [hm]; exact hc5
      · intro p hp
        rcases hnodes5 p hp with hp | hp
        · rcases hst p hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr (by rw [hlvm, hlvn]; omega)
        · exact Or.inr (by rw [hp, hlvm]; exact Nat.le_refl _)
      · intro hlow _
        have hnone : s4.2.nodes.lookup (nw.level + 1, s1.1, s2.1, s3.1, s4.1) = none := by
          apply lookup_none
          intro p hp heq
          rcases hst p hp with hp' | hp'
          · have := hlow p hp'; rw [heq, hlvm] at this; simp only at this; omega
          · rw [heq] at hp'; simp only at hp'; omega
        obtain ⟨rfl, -⟩ := hlast5 hnone
        rw [hm]
        exact last_of_push N4 _ (Or.inr ⟨_, _, _, _, rfl⟩) (by
          obtain ⟨ls, hls, hr, hll, -⟩ := hi4
          have := hr.sizes; have : s4.2.lines.length = ls.length + 1 := by rw [hls]; simp
          omega)

/-! ## Round trip -/

theorem Inv.initial : Inv ⟨[macrocellHeader], [], []⟩ #[] #[] #[] :=
  ⟨[], rfl, Reads.nil, by decide, by simp, by simp⟩

/--
Round trip: a nonempty pattern of smart-constructed nodes, of depth at most 63, that is not a single leaf, reads
back as exactly the same tree, with no warnings. (The writer numbers nodes by line, so the number of lines must
stay below 2 ^ 31.)
-/
theorem macrocell_round_trip_Impl (m : MacroCell) (hcan : Canonical m) (hd : m.depth ≤ 63)
    (hsl : macrocellSingleLeaf m = none) (hne : m ≠ emptyMacroCellUInt32 m.level)
    (hlen : ((⟨[macrocellHeader], [], []⟩ : MacrocellWriterState).addTree m).2.lines.length < 2 ^ 31) :
    deserializeMacrocell (serializeMacrocell m) = ⟨.ok, #[], m⟩ := by
  obtain ⟨N', Lv', IL', hinv, -, hc, -, hlast⟩ := addTree_spec m _ #[] #[] #[] Inv.initial hcan hd hlen
  have hid : ((⟨[macrocellHeader], [], []⟩ : MacrocellWriterState).addTree m).1 ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp only [cellChildA, beq_self_eq_true, ite_true, Option.some.injEq] at hc
    exact hne hc.symm
  obtain ⟨hN, hm⟩ := hlast (by simp) hid
  unfold serializeMacrocell
  simp only [hsl]
  obtain ⟨ls, hls, hr, hll, -⟩ := hinv
  rw [deserializeMacrocell_reads hr _ (by simp [hls]) (by simpa using hll) hN, hm]

/-- A single leaf is written as just its leaf line, and reads back as the leaf in the northwest quadrant. -/
theorem macrocell_round_trip_single_leaf_Impl (m : MacroCell) (leaf : UInt64) (hsl : macrocellSingleLeaf m = some leaf) :
    deserializeMacrocell (serializeMacrocell m) = ⟨.ok, #[], makeLevel4Node leaf 0 0 0⟩ := by
  unfold serializeMacrocell
  simp only [hsl]
  have hr := Reads.leaf leaf Reads.nil
  rw [deserializeMacrocell_reads hr _ (by simp) (by simp) (by simp)]
  rfl

end Algorithm

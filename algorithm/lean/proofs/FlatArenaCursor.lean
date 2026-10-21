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
import proofs.FlatArenaConvert

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# The cell cursor

`cellCursorStepWith` enumerates the live cells of a CellNode one step at a time, so that
`FlatHashLifeCellState`'s iterators are lazy. This file proves that running it until its stack is empty emits the
keys of exactly the cells that `foldCellsLoop` folds over, in the same order, and that every step makes progress.
-/

/-- Whether cell `i` (in row-major order) of the leaf at `(x0, y0)` is live and lies in the window. -/
def rowTest (leaf : UInt64) (x0 y0 l t r b : Int64) (i : UInt32) : Bool :=
  leafContains leaf (i &&& 7) (i >>> 3) && l <= x0 + (i &&& 7).toUInt64.toInt64 &&
    x0 + (i &&& 7).toUInt64.toInt64 < r && t <= y0 + (i >>> 3).toUInt64.toInt64 &&
    y0 + (i >>> 3).toUInt64.toInt64 < b

theorem leafContains_zero (x y : UInt32) : leafContains 0 x y = false := by
  unfold leafContains
  simp

theorem foldLeafCellsLoop_zero {α : Type} (x0 y0 l t r b : Int64) (f : α → UInt64 → α) :
    ∀ (n : ℕ) (i : UInt32) (acc : α), 64 - i.toNat = n → foldLeafCellsLoop 0 x0 y0 l t r b f i acc = acc := by
  intro n
  induction n with
  | zero =>
    intro i acc hn
    rw [foldLeafCellsLoop, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; simp; omega)]
  | succ n ih =>
    intro i acc hn
    have hi : i < 64 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
    rw [foldLeafCellsLoop, dite_eq_left hi]
    simp only [leafContains_zero, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ih (i + 1) acc (by rw [u32_succ_toNat hi]; omega)

/-- The bits of `leafRowMask leaf … i` are the cells `k ≥ i` that `rowTest` accepts. -/
theorem leafRowMask_getLsbD (leaf : UInt64) (x0 y0 l t r b : Int64) :
    ∀ (n : ℕ) (i : UInt32), 64 - i.toNat = n → ∀ k : ℕ,
      (leafRowMask leaf x0 y0 l t r b i).toBitVec.getLsbD k =
        (decide (i.toNat ≤ k) && decide (k < 64) && rowTest leaf x0 y0 l t r b k.toUInt32) := by
  intro n
  induction n with
  | zero =>
    intro i hn k
    rw [leafRowMask, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; simp; omega)]
    have : ¬ (i.toNat ≤ k ∧ k < 64) := by omega
    simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero]
    by_cases h1 : i.toNat ≤ k <;> by_cases h2 : k < 64 <;> simp [h1, h2] <;> omega
  | succ n ih =>
    intro i hn k
    have hi : i < 64 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
    have hi1 := u32_succ_toNat hi
    have hrest := ih (i + 1) (by omega) k
    rw [hi1] at hrest
    rw [leafRowMask, dite_eq_left hi]
    dsimp only
    have hit : (leafContains leaf (i &&& 7) (i >>> 3) && l <= x0 + (i &&& 7).toUInt64.toInt64 &&
        x0 + (i &&& 7).toUInt64.toInt64 < r && t <= y0 + (i >>> 3).toUInt64.toInt64 &&
        y0 + (i >>> 3).toUInt64.toInt64 < b) = rowTest leaf x0 y0 l t r b i := rfl
    rw [hit]
    have hlt : (i.toUInt64).toNat < 64 := by rw [UInt32.toNat_toUInt64]; have := u32_lt_iff.mp hi; simpa using this
    by_cases ek : k = i.toNat
    · subst ek
      have hk : (i.toNat).toUInt32 = i := by simp
      split <;> rename_i hc
      · rw [UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_one_shl _ hlt, hrest, hk, hc]
        simp [UInt32.toNat_toUInt64, show i.toNat < 64 by have := u32_lt_iff.mp hi; simpa using this]
      · rw [hrest, hk]
        simp only [Bool.not_eq_true] at hc
        simp [hc]
    · split
      · rw [UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_one_shl _ hlt, hrest]
        rw [UInt32.toNat_toUInt64]
        by_cases h1 : i.toNat ≤ k
        · have h2 : i.toNat + 1 ≤ k := by omega
          simp [h1, h2, ek]
        · have h2 : ¬ i.toNat + 1 ≤ k := by omega
          simp [h1, h2, ek]
      · rw [hrest]
        by_cases h1 : i.toNat ≤ k
        · have h2 : i.toNat + 1 ≤ k := by omega
          simp [h1, h2]
        · have h2 : ¬ i.toNat + 1 ≤ k := by omega
          simp [h1, h2]

/-- The keys of the cells `k ≥ i` of a `leafRowMask` chunk, in increasing bit order. -/
def chunkKeysFrom (mask : UInt64) (x0 y0 : Int64) (i : ℕ) : List UInt64 :=
  ((List.range' i (64 - i)).filter (fun k => mask.toBitVec.getLsbD k)).map (fun k => leafChunkKey x0 y0 k.toUInt32)

theorem chunkKeys_eq (mask : UInt64) (x0 y0 : Int64) : chunkKeys mask x0 y0 = chunkKeysFrom mask x0 y0 0 := by
  unfold chunkKeys chunkKeysFrom
  rw [List.range_eq_range']

theorem chunkKeysFrom_succ (mask : UInt64) (x0 y0 : Int64) {i : ℕ} (hi : i < 64) :
    chunkKeysFrom mask x0 y0 i =
      (if mask.toBitVec.getLsbD i then [leafChunkKey x0 y0 i.toUInt32] else []) ++ chunkKeysFrom mask x0 y0 (i + 1) := by
  unfold chunkKeysFrom
  rw [show 64 - i = (64 - (i + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  split <;> simp_all

theorem chunkKeysFrom_congr {m m' : UInt64} (x0 y0 : Int64) {i : ℕ}
    (h : ∀ k, i ≤ k → m.toBitVec.getLsbD k = m'.toBitVec.getLsbD k) :
    chunkKeysFrom m x0 y0 i = chunkKeysFrom m' x0 y0 i := by
  unfold chunkKeysFrom
  congr 1
  apply List.filter_congr
  intro k hk
  rw [List.mem_range'_1] at hk
  exact h k hk.1

theorem chunkKeysFrom_end (mask : UInt64) (x0 y0 : Int64) {i : ℕ} (hi : 64 ≤ i) : chunkKeysFrom mask x0 y0 i = [] := by
  unfold chunkKeysFrom
  rw [show 64 - i = 0 by omega]
  rfl

theorem chunkKeys_zero (x0 y0 : Int64) : chunkKeys 0 x0 y0 = [] := by
  unfold chunkKeys
  simp

/-- The leaf fold from cell `i` on folds over the keys of the leaf's `leafRowMask` chunk. -/
theorem foldLeafCellsLoop_chunk {α : Type} (leaf : UInt64) (x0 y0 l t r b : Int64) (f : α → UInt64 → α) :
    ∀ (n : ℕ) (i : UInt32) (acc : α), 64 - i.toNat = n →
      foldLeafCellsLoop leaf x0 y0 l t r b f i acc =
        (chunkKeysFrom (leafRowMask leaf x0 y0 l t r b i) x0 y0 i.toNat).foldl f acc := by
  intro n
  induction n with
  | zero =>
    intro i acc hn
    rw [foldLeafCellsLoop, dite_eq_right (by rw [UInt32.lt_iff_toNat_lt]; simp; omega),
      chunkKeysFrom_end _ _ _ (by omega)]
    rfl
  | succ n ih =>
    intro i acc hn
    have hi : i < 64 := by rw [UInt32.lt_iff_toNat_lt]; simp; omega
    have hi64 : i.toNat < 64 := by have := u32_lt_iff.mp hi; simpa using this
    have hi1 := u32_succ_toNat hi
    rw [foldLeafCellsLoop, dite_eq_left hi]
    dsimp only
    rw [ih (i + 1) _ (by omega), hi1, chunkKeysFrom_succ _ _ _ hi64,
      leafRowMask_getLsbD leaf x0 y0 l t r b _ i rfl i.toNat]
    have hcongr : chunkKeysFrom (leafRowMask leaf x0 y0 l t r b i) x0 y0 (i.toNat + 1) =
        chunkKeysFrom (leafRowMask leaf x0 y0 l t r b (i + 1)) x0 y0 (i.toNat + 1) := by
      apply chunkKeysFrom_congr
      intro k hk
      rw [leafRowMask_getLsbD leaf x0 y0 l t r b _ i rfl k, leafRowMask_getLsbD leaf x0 y0 l t r b _ (i + 1) rfl k,
        hi1]
      have h1 : i.toNat ≤ k := by omega
      simp [h1, hk]
    rw [hcongr]
    have hk : (i.toNat).toUInt32 = i := by simp
    have hit : (leafContains leaf (i &&& 7) (i >>> 3) && l <= x0 + (i &&& 7).toUInt64.toInt64 &&
        x0 + (i &&& 7).toUInt64.toInt64 < r && t <= y0 + (i >>> 3).toUInt64.toInt64 &&
        y0 + (i >>> 3).toUInt64.toInt64 < b) = rowTest leaf x0 y0 l t r b i := rfl
    rw [hit, hk]
    simp only [Nat.le_refl, decide_true, Bool.true_and]
    split <;> rename_i hc <;> simp [hc, leafChunkKey, hi64]

/-- The leaf fold folds over the keys of the leaf's `leafRowMask` chunk. -/
theorem foldLeafCells_chunk {α : Type} (leaf : UInt64) (x0 y0 l t r b : Int64) (f : α → UInt64 → α) (acc : α) :
    foldLeafCellsLoop leaf x0 y0 l t r b f 0 acc = (chunkKeys (leafRowMask leaf x0 y0 l t r b 0) x0 y0).foldl f acc := by
  rw [chunkKeys_eq, foldLeafCellsLoop_chunk leaf x0 y0 l t r b f _ 0 acc rfl]
  rfl


theorem cellChild_eq (a : FlatHashLifeArena) (id : UInt32) :
    a.cellChild id 0 = a.cellNw[id.toNat]! ∧ a.cellChild id 1 = a.cellNe[id.toNat]! ∧
      a.cellChild id 2 = a.cellSw[id.toNat]! ∧ a.cellChild id 3 = a.cellSe[id.toNat]! :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem l4Leaf_eq (a : FlatHashLifeArena) (id : UInt32) :
    a.l4Leaf id 0 = a.l4Nw[id.toNat]! ∧ a.l4Leaf id 1 = a.l4Ne[id.toNat]! ∧
      a.l4Leaf id 2 = a.l4Sw[id.toNat]! ∧ a.l4Leaf id 3 = a.l4Se[id.toNat]! :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem foldStack_pushLeafFrame {α : Type} (a : FlatHashLifeArena) (l t r b : Int64) (f : α → UInt64 → α) (acc : α)
    (bits : UInt64) (x0 y0 : Int64) (rest : List CellFrame) :
    a.foldStack l t r b f acc (pushLeafFrame bits x0 y0 rest) =
      a.foldStack l t r b f (foldLeafCellsLoop bits x0 y0 l t r b f 0 acc) rest := by
  unfold pushLeafFrame
  split
  · rename_i h
    rw [eq_of_beq h, foldLeafCellsLoop_zero x0 y0 l t r b f 64 0 acc rfl]
  · rfl

theorem foldStack_cons {α : Type} (a : FlatHashLifeArena) (l t r b : Int64) (f : α → UInt64 → α) (acc : α)
    (frame : CellFrame) (rest : List CellFrame) :
    a.foldStack l t r b f acc (frame :: rest) = a.foldStack l t r b f (a.foldFrame l t r b f acc frame) rest := rfl

/-- A step of the cursor emits a chunk and leaves a stack that together stand for the cells of the old stack. -/
theorem foldStack_step {α : Type} (a : FlatHashLifeArena) (l t r b : Int64) (f : α → UInt64 → α) (acc : α)
    (frame : CellFrame) (rest : List CellFrame) :
    a.foldStack l t r b f acc (frame :: rest) =
      a.foldStack l t r b f
        ((chunkKeys (a.cellCursorStepWith l t r b (frame :: rest)).1 (a.cellCursorStepWith l t r b (frame :: rest)).2.1
          (a.cellCursorStepWith l t r b (frame :: rest)).2.2.1).foldl f acc)
        (a.cellCursorStepWith l t r b (frame :: rest)).2.2.2 := by
  rw [foldStack_cons]
  cases frame with
  | leaf bits x0 y0 =>
    simp only [FlatHashLifeArena.cellCursorStepWith, FlatHashLifeArena.foldFrame]
    rw [foldLeafCells_chunk]
  | l4 id x0 y0 =>
    simp only [FlatHashLifeArena.cellCursorStepWith, FlatHashLifeArena.foldFrame, (l4Leaf_eq a id).1, (l4Leaf_eq a id).2.1, (l4Leaf_eq a id).2.2.1,
      (l4Leaf_eq a id).2.2.2]
    unfold FlatHashLifeArena.foldLevel4Cells
    split
    · simp [chunkKeys_zero]
    · simp only [chunkKeys_zero, List.foldl_nil, foldStack_pushLeafFrame]
  | node id x0 y0 fuel =>
    simp only [FlatHashLifeArena.cellCursorStepWith, FlatHashLifeArena.foldFrame, (cellChild_eq a id).1, (cellChild_eq a id).2.1,
      (cellChild_eq a id).2.2.1, (cellChild_eq a id).2.2.2]
    rw [FlatHashLifeArena.foldCellsLoop]
    by_cases h0 : fuel = 0
    · simp [h0, chunkKeys_zero]
    · by_cases h1 : id ≥ a.cellCount
      · simp [h0, h1, chunkKeys_zero]
      · simp only [h0, h1, beq_iff_eq, decide_false, Bool.or_false,
          ↓reduceIte, ↓reduceDIte]
        split
        · simp [chunkKeys_zero]
        · split
          · simp [chunkKeys_zero]
          · split <;> simp [chunkKeys_zero, foldStack_cons, FlatHashLifeArena.foldFrame]

/-- A bound on the number of steps the cursor takes on a frame. -/
def frameWeight : CellFrame → ℕ
  | .node _ _ _ fuel => 50 * 5 ^ fuel.toNat
  | .l4 .. => 9
  | .leaf .. => 1

/-- A bound on the number of steps the cursor takes on a stack. -/
def stackWeight (stack : List CellFrame) : ℕ := (stack.map frameWeight).sum

theorem stackWeight_cons (frame : CellFrame) (rest : List CellFrame) :
    stackWeight (frame :: rest) = frameWeight frame + stackWeight rest := by
  simp [stackWeight]

theorem stackWeight_pushLeafFrame (bits : UInt64) (x0 y0 : Int64) (rest : List CellFrame) :
    stackWeight (pushLeafFrame bits x0 y0 rest) ≤ 1 + stackWeight rest := by
  unfold pushLeafFrame
  split
  · omega
  · rw [stackWeight_cons]
    simp [frameWeight]

/-- Every step of the cursor lowers the weight of its stack. -/
theorem stackWeight_step (a : FlatHashLifeArena) (l t r b : Int64) (frame : CellFrame) (rest : List CellFrame) :
    stackWeight (a.cellCursorStepWith l t r b (frame :: rest)).2.2.2 < stackWeight (frame :: rest) := by
  rw [stackWeight_cons]
  cases frame with
  | leaf bits x0 y0 =>
    simp only [FlatHashLifeArena.cellCursorStepWith, frameWeight]
    omega
  | l4 id x0 y0 =>
    simp only [FlatHashLifeArena.cellCursorStepWith, frameWeight, (l4Leaf_eq a id).1, (l4Leaf_eq a id).2.1, (l4Leaf_eq a id).2.2.1,
      (l4Leaf_eq a id).2.2.2]
    split
    · dsimp only; omega
    · have h1 := stackWeight_pushLeafFrame a.l4Se[id.toNat]! (x0 + 8) (y0 + 8) rest
      have h2 := stackWeight_pushLeafFrame a.l4Sw[id.toNat]! x0 (y0 + 8)
        (pushLeafFrame a.l4Se[id.toNat]! (x0 + 8) (y0 + 8) rest)
      have h3 := stackWeight_pushLeafFrame a.l4Ne[id.toNat]! (x0 + 8) y0
        (pushLeafFrame a.l4Sw[id.toNat]! x0 (y0 + 8) (pushLeafFrame a.l4Se[id.toNat]! (x0 + 8) (y0 + 8) rest))
      have h4 := stackWeight_pushLeafFrame a.l4Nw[id.toNat]! x0 y0 (pushLeafFrame a.l4Ne[id.toNat]! (x0 + 8) y0
        (pushLeafFrame a.l4Sw[id.toNat]! x0 (y0 + 8) (pushLeafFrame a.l4Se[id.toNat]! (x0 + 8) (y0 + 8) rest)))
      dsimp only
      omega
  | node id x0 y0 fuel =>
    simp only [FlatHashLifeArena.cellCursorStepWith, frameWeight, (cellChild_eq a id).1, (cellChild_eq a id).2.1,
      (cellChild_eq a id).2.2.1, (cellChild_eq a id).2.2.2]
    have hp : 0 < 5 ^ fuel.toNat := Nat.pow_pos (by omega)
    split
    · dsimp only; omega
    · rename_i h0
      have hf : fuel ≠ 0 := by
        intro e
        simp [e] at h0
      have hfn : fuel.toNat ≠ 0 := fun e => hf (UInt32.toNat_inj.mp (by simpa using e))
      have hf1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_toNat_sub (by simp; omega)
      have h5 : 5 ^ fuel.toNat = 5 * 5 ^ (fuel.toNat - 1) := by
        rw [← Nat.pow_succ']
        congr 1
        omega
      split
      · dsimp only; omega
      · split
        · dsimp only; omega
        · split <;> simp only [stackWeight_cons, frameWeight, hf1] <;> omega

theorem frameWeight_pos (frame : CellFrame) : 1 ≤ frameWeight frame := by
  cases frame with
  | node _ _ _ fuel =>
    have : 0 < 5 ^ fuel.toNat := Nat.pow_pos (by omega)
    simp only [frameWeight]
    omega
  | l4 => simp [frameWeight]
  | leaf => simp [frameWeight]

/--
Running the cursor for at least as many steps as the stack's weight empties the stack, and emits the keys that the
stack's fold folds over, in order.
-/
theorem cellCursorRun_foldStack (a : FlatHashLifeArena) (l t r b : Int64) :
    ∀ (n : ℕ) (stack : List CellFrame), stackWeight stack ≤ n →
      (cellCursorRun (a.cellCursorStepWith l t r b) n stack).2 = [] ∧
      ∀ (α : Type) (f : α → UInt64 → α) (acc : α),
        a.foldStack l t r b f acc stack = (cellCursorRun (a.cellCursorStepWith l t r b) n stack).1.foldl f acc := by
  intro n
  induction n with
  | zero =>
    intro stack hw
    cases stack with
    | nil => exact ⟨rfl, fun _ _ _ => rfl⟩
    | cons frame rest =>
      rw [stackWeight_cons] at hw
      have := frameWeight_pos frame
      omega
  | succ n ih =>
    intro stack hw
    cases stack with
    | nil => exact ⟨rfl, fun _ _ _ => rfl⟩
    | cons frame rest =>
      have hlt := stackWeight_step a l t r b frame rest
      obtain ⟨hdone, hfold⟩ := ih (a.cellCursorStepWith l t r b (frame :: rest)).2.2.2 (by omega)
      refine ⟨hdone, fun α f acc => ?_⟩
      rw [foldStack_step, hfold]
      simp only [cellCursorRun, List.foldl_append]

theorem foldl_snoc {β γ : Type} (g : β → γ) : ∀ (xs : List β) (acc : List γ),
    xs.foldl (fun a x => a ++ [g x]) acc = acc ++ xs.map g
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_snoc g xs, List.map_cons, List.append_assoc]
    rfl

theorem foldl_append_singleton {γ : Type} (xs : List γ) (acc : List γ) :
    xs.foldl (fun a x => a ++ [x]) acc = acc ++ xs := by
  simpa using foldl_snoc id xs acc

/-- Run from `cellCursorStart`, the cursor stops, and emits the keys of the live cells of the state in any window. -/
theorem cellCursor_root_enum {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) (l t r b : Int64) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun (a.cellCursorStepWith l t r b) n (a.cellCursorStart root ox oy) = (L.map enumKey, []) := by
  obtain ⟨L, hnd, hmem, heq⟩ := foldCellsLoop_root_enum hwf hid hlv ox oy l t r b
  refine ⟨L, hnd, hmem, fun n hn => ?_⟩
  obtain ⟨hdone, hfold⟩ := cellCursorRun_foldStack a l t r b n _ hn
  have h := hfold (List UInt64) (fun xs k => xs ++ [k]) []
  have hstart : a.foldStack l t r b (fun xs k => xs ++ [k]) [] (a.cellCursorStart root ox oy) =
      a.foldCellsLoop root ox.toInt64 oy.toInt64 l t r b (fun xs k => xs ++ [k]) [] 64 := rfl
  rw [hstart, heq, foldl_snoc enumKey, foldl_append_singleton] at h
  simp only [List.nil_append] at h
  exact Prod.ext h.symm hdone

/-- The live cells of a state lie within its root, so they have 62-bit coordinates no smaller than `-2 ^ 31`. -/
theorem flatState_cell_bounds {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) {c : Coord} (hc : c ∈ hashLifeToGrid (flatState a ox oy root)) :
    -2 ^ 31 ≤ c.1 ∧ c.1 < 2 ^ 62 ∧ -2 ^ 31 ≤ c.2 ∧ c.2 < 2 ^ 62 := by
  obtain ⟨k, hk, hn⟩ := NodeIs.of_lt' hwf hid
  have hW := hn.WFd
  unfold hashLifeToGrid flatState at hc
  dsimp only at hc
  rw [hn.denoteCell_eq, mem_macroCellToGrid_iff hW (by omega)] at hc
  have hb := cellAt_bounds hW (by omega) hc
  have hp := pow_two_le_pow (show k + 1 + 4 ≤ 61 by omega)
  have h61 : (2 : ℤ) ^ 61 = 2305843009213693952 := by decide
  have hx1 := Int32.le_toInt ox
  have hx2 := Int32.toInt_lt ox
  have hy1 := Int32.le_toInt oy
  have hy2 := Int32.toInt_lt oy
  have h31 : (2 : ℤ) ^ 31 = 2147483648 := by decide
  have h62 : (2 : ℤ) ^ 62 = 4611686018427387904 := by decide
  omega

/--
Run from `cellCursorStart`, the cursor stops, and emits the keys of the live cells of the state in the window, each
once and in a fixed order.
-/
theorem cellCursor_root {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) {l t r b : Int64} (hw : EnumBounds l t r b) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun (a.cellCursorStepWith l t r b) n (a.cellCursorStart root ox oy) = (L.map coordKey, []) := by
  obtain ⟨L, hnd, hmem, heq⟩ := foldCellsLoop_root hwf hid hlv ox oy hw
  refine ⟨L, hnd, hmem, fun n hn => ?_⟩
  obtain ⟨hdone, hfold⟩ := cellCursorRun_foldStack a l t r b n _ hn
  have h := hfold (List UInt64) (fun xs k => xs ++ [k]) []
  have hstart : a.foldStack l t r b (fun xs k => xs ++ [k]) [] (a.cellCursorStart root ox oy) =
      a.foldCellsLoop root ox.toInt64 oy.toInt64 l t r b (fun xs k => xs ++ [k]) [] 64 := rfl
  rw [hstart, heq, foldl_snoc coordKey, foldl_append_singleton] at h
  simp only [List.nil_append] at h
  exact Prod.ext h.symm hdone

/--
`cellCursorStepInWindow` (the iterator of `FlatHashLifeCellState.getAliveCellsInWindow`), run from `cellCursorStart`,
stops and emits the keys of the live cells of the state in the window `[l, r) × [t, b)`, each once and in a fixed
order.
-/
theorem cellCursorInWindow_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy l t r b : Int32) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow l.toInt t.toInt r.toInt b.toInt c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun (a.cellCursorStepInWindow l t r b) n (a.cellCursorStart root ox oy) = (L.map coordKey, []) := by
  have hw : EnumBounds l.toInt64 t.toInt64 r.toInt64 b.toInt64 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Int32.toInt_toInt64]
    · exact Int32.le_toInt l
    · exact Int32.le_toInt t
    · have := Int32.toInt_lt r; omega
    · have := Int32.toInt_lt b; omega
  have := cellCursor_root hwf hid hlv ox oy hw
  simp only [Int32.toInt_toInt64] at this
  exact this

/--
`cellCursorStepAll` (the iterator of `FlatHashLifeCellState.aliveCells`), run from `cellCursorStart`, stops and emits
the keys of the live cells of the state with 32-bit coordinates, each once and in a fixed order.
-/
theorem cellCursorAll_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) :
    ∃ L : List Coord, L.Nodup ∧
      (∀ c, c ∈ L ↔ c ∈ hashLifeToGrid (flatState a ox oy root) ∧ InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) ∧
      ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
        cellCursorRun a.cellCursorStepAll n (a.cellCursorStart root ox oy) = (L.map coordKey, []) := by
  have e1 : (-2147483648 : Int64).toInt = -2 ^ 31 := by decide
  have e2 : (2147483648 : Int64).toInt = 2 ^ 31 := by decide
  have hw : EnumBounds (-2147483648) (-2147483648) 2147483648 2147483648 :=
    ⟨by rw [e1]; decide, by rw [e1]; decide, by rw [e2]; decide, by rw [e2]; decide⟩
  have := cellCursor_root hwf hid hlv ox oy hw
  rw [e1, e2] at this
  exact this

theorem chunkKeys_eq_nil_iff (mask : UInt64) (x0 y0 : Int64) : chunkKeys mask x0 y0 = [] ↔ mask = 0 := by
  constructor
  · intro h
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have : k ∉ (List.range 64).filter (fun k => mask.toBitVec.getLsbD k) := by
      intro hm
      unfold chunkKeys at h
      rw [List.map_eq_nil_iff] at h
      rw [h] at hm
      simp at hm
    simp only [List.mem_filter, List.mem_range, hk, true_and, Bool.not_eq_true] at this
    simp [this]
  · rintro rfl
    exact chunkKeys_zero x0 y0

/--
`FlatHashLifeCellState.fitsInIntRange` runs `cellCursorStepPastX` and `cellCursorStepPastY` from `cellCursorStart`
and finds no emitted cell exactly when every live cell of the state has 32-bit coordinates.
-/
theorem fitsInIntRange_Impl {a : FlatHashLifeArena} (hwf : ArenaWF a) {root : UInt32} (hid : root < a.cellCount)
    (hlv : cellLevelOf a root ≤ 61) (ox oy : Int32) :
    ∀ n, stackWeight (a.cellCursorStart root ox oy) ≤ n →
      (((cellCursorRun a.cellCursorStepPastX n (a.cellCursorStart root ox oy)).1 = [] ∧
        (cellCursorRun a.cellCursorStepPastY n (a.cellCursorStart root ox oy)).1 = []) ↔
      ∀ c ∈ hashLifeToGrid (flatState a ox oy root), InWindow (-2 ^ 31) (-2 ^ 31) (2 ^ 31) (2 ^ 31) c) := by
  intro n hn
  obtain ⟨LX, -, hX, eX⟩ := cellCursor_root_enum hwf hid hlv ox oy 2147483648 (-9223372036854775808)
    9223372036854775807 9223372036854775807
  obtain ⟨LY, -, hY, eY⟩ := cellCursor_root_enum hwf hid hlv ox oy (-9223372036854775808) 2147483648
    9223372036854775807 9223372036854775807
  have rX : cellCursorRun a.cellCursorStepPastX n (a.cellCursorStart root ox oy) = (LX.map enumKey, []) := eX n hn
  have rY : cellCursorRun a.cellCursorStepPastY n (a.cellCursorStart root ox oy) = (LY.map enumKey, []) := eY n hn
  rw [rX, rY]
  dsimp only
  rw [List.map_eq_nil_iff, List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  have e1 : (2147483648 : Int64).toInt = 2 ^ 31 := by decide
  have e2 : (-9223372036854775808 : Int64).toInt = -2 ^ 63 := by decide
  have e3 : (9223372036854775807 : Int64).toInt = 2 ^ 63 - 1 := by decide
  rw [e1, e2, e3] at hX
  rw [e1, e2, e3] at hY
  constructor
  · rintro ⟨nX, nY⟩ c hc
    have hb := flatState_cell_bounds hwf hid hlv ox oy hc
    have h1 : ¬ (2 ^ 31 ≤ c.1) := fun h => nX c ((hX c).mpr ⟨hc, h, by omega, by omega, by omega⟩)
    have h2 : ¬ (2 ^ 31 ≤ c.2) := fun h => nY c ((hY c).mpr ⟨hc, by omega, by omega, h, by omega⟩)
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨hg, hw, _⟩ := (hX c).mp hc
      have := (h c hg).2.1
      omega
    · obtain ⟨hg, _, _, hw, _⟩ := (hY c).mp hc
      have := (h c hg).2.2.2
      omega

end Algorithm

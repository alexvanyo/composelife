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

import Algorithm.FlatHashLife
import AlgorithmDefs
import proofs.FlatArenaBasics
import proofs.FlatArenaIntern
import proofs.FlatArenaStep
import proofs.FlatArenaGeneration
import proofs.FlatArenaCopy

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/-!
# Flat HashLife arena: the step budget

`stepCellSerialLoop` stops early when its step budget (`fuel`) or its work stack runs out, and `stepCellSerial`
reports that as a failure through `overflow`, the same flag that reports a full node table. This module proves
neither limit is ever reached when the work stack has room for 26 entries and the CellNode table has at most
`2 ^ 28` slots: the engine then fails only when a node table is full (`ArenaFull`). The subgraph copy loop
`copyCellFromLoop` has the same kind of budget and stack, and the same argument (with remapped source CellNodes
in place of memoized ones) shows that copying and compaction also fail only when a node table is full.

The argument is a potential function. Let `M` be the CellNode capacity, `memoCount` the number of memoized
CellNodes, `k` the stack depth and `memoStack` the number of memoized stack entries. Then

  `pot = 2 * (M - memoCount) + 2 * memoStack - k`

decreases by at least one on every iteration: memoizing the top and popping it trades a memo for a stack slot,
popping an already memoized top drops `memoStack`, and pushing an unmemoized child grows `k`. Stack entries are
distinct (each is a quadrant of the one below it, so their levels strictly decrease), so newly memoized nodes
are counted at most once on the stack. Entry levels also bound the stack depth by the root level minus four.
-/

-- =========================================================================
-- Counting
-- =========================================================================

/-- Counting the elements of a duplicate-free list that satisfy `r`: at most as many as in any list containing it. -/
theorem countP_le_of_nodup_subset (r : ℕ → Bool) :
    ∀ (l L : List ℕ), l.Nodup → (∀ x ∈ l, x ∈ L) → l.countP r ≤ L.countP r
  | [], _, _, _ => by simp
  | x :: t, L, hnd, hsub => by
    have hx : x ∈ L := hsub x (List.mem_cons_self ..)
    have hperm := (List.perm_cons_erase hx).countP_eq r
    rw [hperm]
    have hxt : x ∉ t := (List.nodup_cons.mp hnd).1
    have ht := countP_le_of_nodup_subset r t (L.erase x) (List.nodup_cons.mp hnd).2 (fun y hy => by
      have hne : y ≠ x := fun h => hxt (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy)))
    simp only [List.countP_cons]
    omega

/-- Splitting a count along a weaker predicate. -/
theorem countP_split (p q : ℕ → Bool) :
    ∀ (l : List ℕ), (∀ x ∈ l, p x = true → q x = true) →
      l.countP q = l.countP p + l.countP (fun x => q x && !p x)
  | [], _ => by simp
  | x :: t, h => by
    have ih := countP_split p q t (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self ..)
    simp only [List.countP_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

-- =========================================================================
-- The potential
-- =========================================================================

/-- Whether CellNode slot `j` holds a memoized step result. -/
def memoAt (b : FlatHashLifeArena) (j : ℕ) : Bool := b.cellStepRes[j]! != UNCOMPUTED

/-- The number of CellNodes with a memoized step result. -/
def memoCount (b : FlatHashLifeArena) : ℕ := (List.range b.cellCount.toNat).countP (memoAt b)

/-- The CellNode ids on the work stack `remapL4[0 ..< k]`. -/
def stk (b : FlatHashLifeArena) (k : ℕ) : List ℕ := (List.range k).map fun i => (b.remapL4[i]!).toNat

/-- The number of work-stack entries with a memoized step result. -/
def memoStack (b : FlatHashLifeArena) (k : ℕ) : ℕ := (stk b k).countP (memoAt b)

/--
The work stack of `stepCellSerialLoop` from a root of level `L0`: entry `i` is a CellNode of level `L0 - i` (each
entry is a quadrant of the one below it).
-/
def StackInv (b : FlatHashLifeArena) (k L0 : ℕ) : Prop :=
  k ≤ b.remapL4.size ∧ ∀ i < k, b.remapL4[i]! < b.cellCount ∧ cellLevelOf b b.remapL4[i]! = L0 - i

/--
The potential of the work-stack loop: every iteration that does not end the loop decreases it by at least one.
-/
def pot (b : FlatHashLifeArena) (k : ℕ) : ℤ :=
  2 * ((b.cellMask.toNat + 1 : ℕ) : ℤ) - 2 * (memoCount b : ℤ) + 2 * (memoStack b k : ℤ) - (k : ℤ)

theorem stk_succ (b : FlatHashLifeArena) (k : ℕ) : stk b (k + 1) = stk b k ++ [(b.remapL4[k]!).toNat] := by
  simp [stk, List.range_succ]

theorem StackInv.lt {b : FlatHashLifeArena} {k L0 : ℕ} (h : StackInv b k L0) {i : ℕ} (hi : i < k) :
    b.remapL4[i]! < b.cellCount := (h.2 i hi).1

theorem StackInv.mono {b : FlatHashLifeArena} {k L0 : ℕ} (h : StackInv b (k + 1) L0) : StackInv b k L0 :=
  ⟨by have := h.1; omega, fun i hi => h.2 i (by omega)⟩

theorem StackInv.bound {b : FlatHashLifeArena} (hwf : ArenaWF b) {k L0 : ℕ} (h : StackInv b k L0) (hk : 1 ≤ k) :
    k + 4 ≤ L0 := by
  have h5 := cellLevelOf_ge_five hwf (h.lt (i := k - 1) (by omega))
  rw [(h.2 (k - 1) (by omega)).2] at h5
  omega

theorem stk_nodup {b : FlatHashLifeArena} (hwf : ArenaWF b) {L0 : ℕ} :
    ∀ k, StackInv b k L0 → (stk b k).Nodup
  | 0, _ => by simp [stk]
  | k + 1, h => by
    have hb := h.bound hwf (by omega)
    rw [stk_succ, List.nodup_append]
    refine ⟨stk_nodup hwf k h.mono, by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hxy hy
    simp only [stk, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, he⟩ := hx
    have e : b.remapL4[i]! = b.remapL4[k]! := UInt32.toNat_inj.mp he
    have l1 := (h.2 i (by omega)).2
    have l2 := (h.2 k (by omega)).2
    rw [e] at l1
    omega

theorem memoCount_le {b : FlatHashLifeArena} (hwf : ArenaWF b) : memoCount b ≤ b.cellMask.toNat + 1 :=
  Nat.le_trans List.countP_le_length (by simp; exact hwf.cellCountLe)

theorem pot_lower {b : FlatHashLifeArena} (hwf : ArenaWF b) (k : ℕ) : -(k : ℤ) ≤ pot b k := by
  have := memoCount_le hwf
  unfold pot
  omega

theorem grows_pot {b b' : FlatHashLifeArena} (hwf : ArenaWF b) (g : Grows b b') {k L0 : ℕ} (h : StackInv b k L0) :
    StackInv b' k L0 ∧ pot b' k ≤ pot b k := by
  have hstk : stk b' k = stk b k := by simp only [stk, g.remapL4]
  have hinv : StackInv b' k L0 := ⟨by rw [g.remapL4]; exact h.1, fun i hi => by
    rw [g.remapL4]
    exact ⟨g.ext.cell_lt (h.lt hi), by rw [g.ext.cellLevelOf (h.lt hi)]; exact (h.2 i hi).2⟩⟩
  refine ⟨hinv, ?_⟩
  have hnd := stk_nodup hwf k h
  have hmono : ∀ x, x < b.cellCount.toNat → memoAt b x = true → memoAt b' x = true := by
    intro x hx hm
    simp only [memoAt, bne_iff_ne, ne_eq] at hm ⊢
    exact g.memo x hx hm
  have hstk_lt : ∀ x ∈ stk b k, x < b.cellCount.toNat := by
    intro x hx
    simp only [stk, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact u32_lt_iff.mp (h.lt hi)
  have e1 : memoStack b' k = memoStack b k + (stk b k).countP (fun x => memoAt b' x && !memoAt b x) := by
    unfold memoStack
    rw [hstk]
    exact countP_split _ _ _ (fun x hx => hmono x (hstk_lt x hx))
  have e2 : (List.range b.cellCount.toNat).countP (memoAt b') =
      memoCount b + (List.range b.cellCount.toNat).countP (fun x => memoAt b' x && !memoAt b x) :=
    countP_split _ _ _ (fun x hx => hmono x (List.mem_range.mp hx))
  have e3 : (List.range b.cellCount.toNat).countP (memoAt b') ≤ memoCount b' :=
    (List.range_sublist.mpr g.ext.cellCount).countP_le
  have e4 := countP_le_of_nodup_subset (fun x => memoAt b' x && !memoAt b x) (stk b k)
    (List.range b.cellCount.toNat) hnd (fun x hx => List.mem_range.mpr (hstk_lt x hx))
  unfold pot
  rw [g.masks.2]
  omega

theorem memoStack_succ (b : FlatHashLifeArena) (k : ℕ) :
    memoStack b (k + 1) = memoStack b k + if memoAt b (b.remapL4[k]!).toNat then 1 else 0 := by
  unfold memoStack
  rw [stk_succ, List.countP_append]
  simp only [List.countP_cons, List.countP_nil]
  split <;> simp_all

/-- Popping a memoized entry decreases the potential by one. -/
theorem pot_pop {b : FlatHashLifeArena} {k : ℕ} (hm : memoAt b (b.remapL4[k]!).toNat = true) :
    pot b k = pot b (k + 1) - 1 := by
  unfold pot
  rw [memoStack_succ]
  simp only [hm, ite_true]
  push_cast
  omega

/-- Pushing an unmemoized child of the right level keeps the stack invariant and decreases the potential by one. -/
theorem push_pot {b : FlatHashLifeArena} {k L0 : ℕ} (h : StackInv b k L0) {sp : UInt32} (hsp : sp.toNat = k)
    (hk : k < b.remapL4.size) {c : UInt32} (hc : c < b.cellCount) (hl : cellLevelOf b c = L0 - k)
    (hm : memoAt b c.toNat = false) :
    StackInv (b.setRemapL4 sp c) (k + 1) L0 ∧ pot (b.setRemapL4 sp c) (k + 1) = pot b k - 1 := by
  have hget : ∀ i, i < k → (b.setRemapL4 sp c).remapL4[i]! = b.remapL4[i]! := fun i hi => by
    show (b.remapL4.set! sp.toNat c)[i]! = b.remapL4[i]!
    exact getElem!_set!_ne _ _ _ _ (by omega)
  have htop : (b.setRemapL4 sp c).remapL4[k]! = c := by
    show (b.remapL4.set! sp.toNat c)[k]! = c
    rw [hsp]
    exact getElem!_set!_self _ _ _ hk
  have hsize : (b.setRemapL4 sp c).remapL4.size = b.remapL4.size := size_set! _ _ _
  have hlev : ∀ x, cellLevelOf (b.setRemapL4 sp c) x = cellLevelOf b x := fun _ => rfl
  refine ⟨⟨by omega, fun i hi => ?_⟩, ?_⟩
  · rw [hlev]
    by_cases e : i = k
    · subst e
      rw [htop]
      exact ⟨hc, hl⟩
    · rw [hget i (by omega)]
      exact h.2 i (by omega)
  · have hstk : stk (b.setRemapL4 sp c) k = stk b k := by
      unfold stk
      apply List.map_congr_left
      intro i hi
      rw [hget i (List.mem_range.mp hi)]
    have hmemo : memoAt (b.setRemapL4 sp c) = memoAt b := rfl
    unfold pot
    rw [memoStack_succ, htop, hmemo, hm]
    unfold memoStack
    rw [hstk, hmemo]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    have : memoCount (b.setRemapL4 sp c) = memoCount b := rfl
    have hmask : (b.setRemapL4 sp c).cellMask = b.cellMask := rfl
    rw [this, hmask]
    push_cast
    omega

/-- A loop whose `overflow` flag is set returns its arena unchanged. -/
theorem stepCellSerialLoop_overflow {b : FlatHashLifeArena} (h : b.overflow ≠ 0) (sp stackLimit fuel : UInt32) :
    b.stepCellSerialLoop sp stackLimit fuel = b := by
  rw [FlatHashLifeArena.stepCellSerialLoop.eq_1]
  split
  · rfl
  · simp [h]

/-- An empty-stack loop returns its arena unchanged. -/
theorem stepCellSerialLoop_empty (b : FlatHashLifeArena) (stackLimit fuel : UInt32) :
    b.stepCellSerialLoop 0 stackLimit fuel = b := by
  rw [FlatHashLifeArena.stepCellSerialLoop.eq_1]
  split
  · rfl
  · simp

-- =========================================================================
-- The work-stack loop
-- =========================================================================

theorem u32_sub_one_toNat {n : UInt32} (h : 1 ≤ n.toNat) : (n - 1).toNat = n.toNat - 1 := by
  have h1 : (1 : UInt32) ≤ n := by
    rw [UInt32.le_iff_toNat_le]
    simpa using h
  rw [UInt32.toNat_sub_of_le n 1 h1]
  rfl

theorem StackInv.le {b : FlatHashLifeArena} {k j L0 : ℕ} (h : StackInv b k L0) (hj : j ≤ k) : StackInv b j L0 :=
  ⟨by have := h.1; omega, fun i hi => h.2 i (by omega)⟩

/-- What the work-stack loop guarantees about the arena `r` it returns, for the root `root` at the stack bottom. -/
def LoopGoal (r : FlatHashLifeArena) (root : UInt32) : Prop :=
  (r.overflow = 0 → memoAt r root.toNat = true) ∧ (r.overflow ≠ 0 → ArenaFull r)

/-- A state of the work-stack loop with `k` entries, from a root of level `L0`. -/
structure LoopState (b : FlatHashLifeArena) (k L0 : ℕ) (root stackLimit : UInt32) : Prop where
  wf : ArenaWF b
  ovf : b.overflow = 0
  inv : StackInv b k L0
  pos : 1 ≤ k
  root : b.remapL4[0]! = root
  lvl : L0 ≤ b.remapL4.size + 4
  lim : stackLimit.toNat = b.remapL4.size

/-- The work-stack loop meets `LoopGoal` from every state whose potential fits in `fuel`. -/
def LoopIH (L0 : ℕ) (root stackLimit fuel : UInt32) : Prop :=
  ∀ (b : FlatHashLifeArena) (sp : UInt32), LoopState b sp.toNat L0 root stackLimit →
    pot b sp.toNat + L0 ≤ fuel.toNat → LoopGoal (b.stepCellSerialLoop sp stackLimit fuel) root

/-- Popping the top entry after it was memoized (or after the arena filled up). -/
theorem loop_pop {L0 : ℕ} {root stackLimit fuel : UInt32} (ih : LoopIH L0 root stackLimit fuel)
    {b b' : FlatHashLifeArena} {sp : UInt32} (hs : LoopState b sp.toNat L0 root stackLimit)
    (hfuel : pot b sp.toNat + L0 ≤ fuel.toNat + 1) (g : Grows b b')
    (hm : b'.overflow = 0 → memoAt b' (b.remapL4[sp.toNat - 1]!).toNat = true) :
    LoopGoal (b'.stepCellSerialLoop (sp - 1) stackLimit fuel) root := by
  by_cases hov : b'.overflow = 0
  · have hm' := hm hov
    have hsp : (sp - 1).toNat = sp.toNat - 1 := u32_sub_one_toNat hs.pos
    obtain ⟨hinv', hpot⟩ := grows_pot hs.wf g hs.inv
    have e : sp.toNat - 1 + 1 = sp.toNat := by have := hs.pos; omega
    have hpop := pot_pop (b := b') (k := sp.toNat - 1) (by rw [g.remapL4]; exact hm')
    rw [e] at hpop
    by_cases hk : sp.toNat - 1 = 0
    · have hsp0 : sp - 1 = 0 := u32_eq_of_toNat (by rw [hsp, hk]; rfl)
      rw [hsp0, stepCellSerialLoop_empty]
      refine ⟨fun _ => ?_, fun h => absurd hov h⟩
      rw [← hs.root, ← hk]
      exact hm'
    · apply ih b' (sp - 1)
      · rw [hsp]
        exact ⟨g.wf, hov, hinv'.le (by omega), by omega, by rw [g.remapL4]; exact hs.root,
          by rw [g.remapL4]; exact hs.lvl, by rw [g.remapL4]; exact hs.lim⟩
      · rw [hsp]
        omega
  · rw [stepCellSerialLoop_overflow hov]
    exact ⟨fun h => absurd h hov, fun _ => (g.cap hov).resolve_left (fun h => h hs.ovf)⟩

/-- Pushing an unmemoized quadrant of the top entry. -/
theorem loop_push {L0 : ℕ} {root stackLimit fuel : UInt32} (ih : LoopIH L0 root stackLimit fuel)
    {b b4 : FlatHashLifeArena} {sp : UInt32} (hs : LoopState b sp.toNat L0 root stackLimit)
    (hfuel : pot b sp.toNat + L0 ≤ fuel.toNat + 1) (g : Grows b b4) (hov : b4.overflow = 0)
    (hlt : sp.toNat < b.remapL4.size) {c : UInt32} (hc : c < b4.cellCount)
    (hl : cellLevelOf b4 c = L0 - sp.toNat) (hm : memoAt b4 c.toNat = false) :
    LoopGoal ((b4.setRemapL4 sp c).stepCellSerialLoop (sp + 1) stackLimit fuel) root := by
  obtain ⟨hinv4, hpot4⟩ := grows_pot hs.wf g hs.inv
  have hlt4 : sp.toNat < b4.remapL4.size := by rw [g.remapL4]; exact hlt
  obtain ⟨hinv5, hpot5⟩ := push_pot hinv4 rfl hlt4 hc hl hm
  have hsp : (sp + 1).toNat = sp.toNat + 1 :=
    u32_toNat_add_one (by have := hs.lim; have := u32_toNat_lt stackLimit; omega)
  apply ih
  · rw [hsp]
    refine ⟨g.wf.setRemapL4 _ _, hov, hinv5, by omega, ?_, ?_, ?_⟩
    · show (b4.remapL4.set! sp.toNat c)[0]! = root
      rw [getElem!_set!_ne _ _ _ _ (by have := hs.pos; omega), g.remapL4]
      exact hs.root
    · show L0 ≤ (b4.remapL4.set! sp.toNat c).size + 4
      rw [size_set!, g.remapL4]
      exact hs.lvl
    · show stackLimit.toNat = (b4.remapL4.set! sp.toNat c).size
      rw [size_set!, g.remapL4]
      exact hs.lim
  · rw [hsp]
    omega

theorem memoAt_of_getCellStepRes {a : FlatHashLifeArena} {c : UInt32} (hc : c < a.cellCount)
    (hr : getCellStepRes a c = UNCOMPUTED) : memoAt a c.toNat = false := by
  unfold getCellStepRes at hr
  rw [ite_eq_left hc] at hr
  simp [memoAt, hr]

/--
The work-stack loop runs out of neither step budget nor stack space: started on a root of level `L0` with enough
`fuel` for the potential, it either memoizes the root or stops because a node table is full.
-/
theorem stepCellSerialLoop_budget (L0 : ℕ) (root stackLimit : UInt32) (n : ℕ) :
    ∀ fuel : UInt32, fuel.toNat ≤ n → LoopIH L0 root stackLimit fuel := by
  induction n with
  | zero =>
    intro fuel hn b sp hs hfuel
    exfalso
    have := pot_lower hs.wf sp.toNat
    have := hs.inv.bound hs.wf hs.pos
    omega
  | succ n ih =>
    intro fuel hn b sp hs hfuel
    have hf : fuel ≠ 0 := by
      intro h
      subst h
      have := pot_lower hs.wf sp.toNat
      have := hs.inv.bound hs.wf hs.pos
      simp at hfuel
      omega
    have hf1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub_one_toNat (by
      have : fuel.toNat ≠ 0 := fun h => hf (u32_eq_of_toNat (by simpa using h))
      omega)
    have hfuel' : pot b sp.toNat + L0 ≤ (fuel - 1).toNat + 1 := by
      rw [hf1]
      have : fuel.toNat ≠ 0 := fun h => hf (u32_eq_of_toNat (by simpa using h))
      omega
    have ih' := ih (fuel - 1) (by omega)
    rw [FlatHashLifeArena.stepCellSerialLoop.eq_1]
    simp only [hf, dite_false]
    have hsp0 : sp ≠ 0 := fun h => by
      have := hs.pos
      subst h
      simp at this
    have hcond : (sp == 0 || b.overflow != 0) = false := by simp [hsp0, hs.ovf]
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    have htop : (sp - 1).toNat = sp.toNat - 1 := u32_sub_one_toNat hs.pos
    have hid : b.remapL4[(sp - 1).toNat]! < b.cellCount := by
      rw [htop]
      exact hs.inv.lt (by have := hs.pos; omega)
    have hlev0 := (hs.inv.2 (sp.toNat - 1) (by have := hs.pos; omega)).2
    rw [← htop] at hlev0
    rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hid; omega)]
    obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hs.wf hid
    split
    · rename_i hmemo
      exact loop_pop ih' hs hfuel' (Grows.refl hs.wf) (fun _ => by rw [← htop]; simpa [memoAt] using hmemo)
    · split
      · -- level 5
        rename_i hle
        have hk0 : k = 0 := by
          have := u8_le_iff.mp hle
          unfold cellLevelOf at hk
          have h5 : (5 : UInt8).toNat = 5 := rfl
          omega
        subst hk0
        rcases e : b.stepLevel5 b.remapL4[(sp - 1).toNat]! with ⟨r, a1⟩
        have s := stepLevel5_spec hs.wf hnode
        rw [e] at s
        exact loop_pop ih' hs hfuel' s.1 (fun h => by rw [← htop]; simpa [memoAt] using s.2.2 h)
      · -- level ≥ 6
        rename_i hle
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
          have := mt u8_le_iff.mpr hle
          unfold cellLevelOf at hk
          have h5 : (5 : UInt8).toNat = 5 := rfl
          exact ⟨k - 1, by omega⟩
        have hwf := hs.wf
        rcases e1 : b.quadrantNW b.remapL4[(sp - 1).toNat]! with ⟨q1, a1⟩
        have s1 := quadrantNW_spec hwf hnode
        rw [e1] at s1
        obtain ⟨g1, r1⟩ := s1
        have w1 := g1.wf
        rcases e2 : a1.quadrantNE b.remapL4[(sp - 1).toNat]! with ⟨q2, a2⟩
        have s2 := quadrantNE_spec w1 (g1.node hwf hnode)
        rw [e2] at s2
        obtain ⟨g2, r2⟩ := s2
        have w2 := g2.wf
        rcases e3 : a2.quadrantSW b.remapL4[(sp - 1).toNat]! with ⟨q3, a3⟩
        have s3 := quadrantSW_spec w2 ((g1.trans g2).node hwf hnode)
        rw [e3] at s3
        obtain ⟨g3, r3⟩ := s3
        have w3 := g3.wf
        rcases e4 : a3.quadrantSE b.remapL4[(sp - 1).toNat]! with ⟨q4, a4⟩
        have s4 := quadrantSE_spec w3 (((g1.trans g2).trans g3).node hwf hnode)
        rw [e4] at s4
        obtain ⟨g4, r4⟩ := s4
        have w4 := g4.wf
        dsimp only at g1 g2 g3 g4 r1 r2 r3 r4 w1 w2 w3 w4 ⊢
        have g14 := ((g1.trans g2).trans g3).trans g4
        split
        · rename_i hov
          have hov4 : a4.overflow ≠ 0 := by simpa using hov
          rw [stepCellSerialLoop_empty]
          exact ⟨fun h => absurd h hov4, fun _ => (g14.cap hov4).resolve_left (fun h => h hs.ovf)⟩
        · rename_i hov
          have hov4 : a4.overflow = 0 := by simpa using hov
          have hov3 := g4.ovf hov4
          have hov2 := g3.ovf hov3
          have hov1 := g2.ovf hov2
          have n1 := ((g2.trans g3).trans g4).node w1 (r1 hov1)
          have n2 := (g3.trans g4).node w2 (r2 hov2)
          have n3 := g4.node w3 (r3 hov3)
          have n4 := r4 hov4
          have hlvq : j + 5 = L0 - sp.toNat := by
            rw [hk] at hlev0
            rw [htop] at hlev0
            have := hs.pos
            omega
          have hlt : sp.toNat < b.remapL4.size := by
            have := hs.lvl
            rw [hk] at hlev0
            rw [htop] at hlev0
            omega
          have push : ∀ c : UInt32, (∃ M, NodeIs a4 (j + 1) c M) → getCellStepRes a4 c = UNCOMPUTED →
              LoopGoal ((a4.setRemapL4 sp c).stepCellSerialLoop (sp + 1) stackLimit (fuel - 1)) root := by
            rintro c ⟨M, hc⟩ hr
            exact loop_push ih' hs hfuel' g14 hov4 hlt hc.lt_cell (by rw [hc.level]; exact hlvq)
              (memoAt_of_getCellStepRes hc.lt_cell hr)
          split
          · rename_i hany
            split
            · rename_i hfull
              exfalso
              rw [ge_iff_le, u32_le_iff, hs.lim] at hfull
              omega
            · split
              · rename_i h1
                exact push q1 ⟨_, n1⟩ (by simpa using h1)
              · split
                · rename_i _ h2
                  exact push q2 ⟨_, n2⟩ (by simpa using h2)
                · split
                  · rename_i _ _ h3
                    exact push q3 ⟨_, n3⟩ (by simpa using h3)
                  · rename_i h1 h2 h3
                    simp only [Bool.or_eq_true, beq_iff_eq] at hany h1 h2 h3
                    exact push q4 ⟨_, n4⟩ (hany.resolve_left fun h => h.elim (fun h => h.elim h1 h2) h3)
          · rename_i hall
            simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hall
            obtain ⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩ := hall
            have m1 := getCellStepRes_memo w4 n1 hr1
            have m2 := getCellStepRes_memo w4 n2 hr2
            have m3 := getCellStepRes_memo w4 n3 hr3
            have m4 := getCellStepRes_memo w4 n4 hr4
            have hlv : a4.cellLevel[(b.remapL4[(sp - 1).toNat]!).toNat]! =
                b.cellLevel[(b.remapL4[(sp - 1).toNat]!).toNat]! :=
              (g14.ext.cell _ (u32_lt_iff.mp hid)).2.2.2.2
            have gc := combineQuadrants_spec w4 (g14.node hwf hnode) n1 n2 n3 n4 m1 m2 m3 m4
            rw [hlv] at gc
            rcases e5 : a4.combineQuadrants b.remapL4[(sp - 1).toNat]!
                b.cellLevel[(b.remapL4[(sp - 1).toNat]!).toNat]! (getCellStepRes a4 q1)
                (getCellStepRes a4 q2) (getCellStepRes a4 q3) (getCellStepRes a4 q4) with ⟨res, a5⟩
            rw [e5] at gc
            exact loop_pop ih' hs hfuel' (g14.trans gc.1) (fun h => by rw [← htop]; simpa [memoAt] using gc.2 h)

theorem memoStack_le (b : FlatHashLifeArena) (k : ℕ) : memoStack b k ≤ k := by
  have := List.countP_le_length (p := memoAt b) (l := stk b k)
  simpa [memoStack, stk] using this

/--
`stepCellSerial` on a node of level `h + 5` fails only when a node table is full, provided the work stack
`remapL4` has room for `h + 1` entries and the CellNode table has at most `2 ^ 28` slots (so the step budget
`(cellMask + 1) * 8 + 1024` does not wrap around).
-/
theorem stepCellSerial_budget {a : FlatHashLifeArena} (hwf : ArenaWF a) (hov : a.overflow = 0) {h : ℕ}
    {id : UInt32} {m : MacroCell} (hn : NodeIs a (h + 1) id m) (hsz : h + 1 ≤ a.remapL4.size)
    (hsz' : a.remapL4.size < 2 ^ 32) (hmask : a.cellMask.toNat < 2 ^ 28) :
    (a.stepCellSerial id).2.overflow ≠ 0 → ArenaFull (a.stepCellSerial id).2 := by
  have hl := hn.level
  have h256 : h + 5 < 256 := by
    have := u8_toNat_lt (a.cellLevel[id.toNat]!)
    unfold cellLevelOf at hl
    omega
  have hlim : a.remapL4.size.toUInt32.toNat = a.remapL4.size := by
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
    omega
  have hne : a.remapL4.size.toUInt32 ≠ 0 := fun h0 => by
    have := congrArg UInt32.toNat h0
    rw [hlim, UInt32.toNat_zero] at this
    omega
  unfold FlatHashLifeArena.stepCellSerial
  rw [ite_eq_right (by simpa using hne)]
  dsimp only
  have hfuel : ((a.cellMask + 1) * 8 + 1024).toNat = (a.cellMask.toNat + 1) * 8 + 1024 := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.reduceToNat]
    omega
  have hsize0 : 0 < a.remapL4.size := by omega
  have hroot : (a.setRemapL4 0 id).remapL4[0]! = id := getElem!_set!_self _ _ _ hsize0
  have hsz0 : (a.setRemapL4 0 id).remapL4.size = a.remapL4.size := size_set! _ _ _
  have hs0 : LoopState (a.setRemapL4 0 id) (UInt32.toNat 1) (h + 5) id a.remapL4.size.toUInt32 := by
    refine ⟨hwf.setRemapL4 0 id, hov, ⟨?_, fun i hi => ?_⟩, by decide, hroot, by omega, by rw [hsz0]; exact hlim⟩
    · rw [hsz0]
      simp only [UInt32.reduceToNat]
      omega
    · simp only [UInt32.reduceToNat] at hi
      obtain rfl : i = 0 := by omega
      rw [hroot]
      exact ⟨hn.lt_cell, hl⟩
  have hpot : pot (a.setRemapL4 0 id) (UInt32.toNat 1) + ((h + 5 : ℕ) : ℤ) ≤
      (((a.cellMask + 1) * 8 + 1024).toNat : ℤ) := by
    rw [hfuel]
    have := memoStack_le (a.setRemapL4 0 id) 1
    unfold pot
    have hm : (a.setRemapL4 0 id).cellMask = a.cellMask := rfl
    rw [hm]
    simp only [UInt32.reduceToNat]
    omega
  have G := stepCellSerialLoop_budget (h + 5) id a.remapL4.size.toUInt32 _ _ (Nat.le_refl _) _ 1 hs0 hpot
  have l1 := stepCellSerialLoop_spec (a.remapL4.size.toUInt32)
    ((a.cellMask + 1) * 8 + 1024).toNat (a.setRemapL4 0 id) 1 ((a.cellMask + 1) * 8 + 1024) (Nat.le_refl _)
    (hwf.setRemapL4 0 id)
  have hid1 := l1.ext.cell_lt (show id < (a.setRemapL4 0 id).cellCount from hn.lt_cell)
  generalize (a.setRemapL4 0 id).stepCellSerialLoop 1 a.remapL4.size.toUInt32 ((a.cellMask + 1) * 8 + 1024) = a1
    at G l1 hid1
  split
  · rename_i hc
    intro _
    show ArenaFull a1
    by_cases ho : a1.overflow = 0
    · exfalso
      have hm := G.1 ho
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      rcases hc with hc | hc
      · exact hc ho
      · unfold getCellStepRes at hc
        rw [ite_eq_left hid1] at hc
        simp [memoAt, hc] at hm
    · exact G.2 ho
  · rename_i hc
    intro h'
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at hc
    exact absurd hc.1 h'

/--
`stepOneGeneration` fails only when the arena had already failed or a node table is full, provided the work
stack `remapL4` has room for 26 entries and the CellNode table has at most `2 ^ 28` slots.
-/
theorem stepOneGeneration_budget {a : FlatHashLifeArena} (hwf : ArenaWF a) (ox oy : Int32) (root : UInt32)
    (hsz : 26 ≤ a.remapL4.size) (hsz' : a.remapL4.size < 2 ^ 32) (hmask : a.cellMask.toNat < 2 ^ 28) :
    (a.stepOneGeneration ox oy root).2.overflow ≠ 0 →
      a.overflow ≠ 0 ∨ ArenaFull (a.stepOneGeneration ox oy root).2 := by
  by_cases hov : a.overflow ≠ 0
  · exact fun _ => Or.inl hov
  have hov : a.overflow = 0 := by simpa using hov
  unfold FlatHashLifeArena.stepOneGeneration
  split
  · exact Or.inl
  rename_i hroot
  have hid : root < a.cellCount := by
    rw [ge_iff_le, u32_le_iff] at hroot
    rw [u32_lt_iff]
    omega
  obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hwf hid
  have hLnat : (a.cellLevel[root.toNat]!.toUInt32).toNat = k + 5 := by
    rw [u8_toUInt32_toNat]
    exact hk
  have hk256 : k + 5 < 256 := by
    have := u8_toNat_lt (a.cellLevel[root.toNat]!)
    unfold cellLevelOf at hk
    omega
  dsimp only
  split
  · -- expanded
    split
    · exact Or.inl
    rename_i hK
    have hK' : k + 7 ≤ 30 := by
      have h2 : (2 : UInt32).toNat = 2 := rfl
      rw [gt_iff_lt, u32_lt_iff, u32_toNat_add (by rw [hLnat, h2]; omega), hLnat] at hK
      simp at hK
      omega
    split
    · exact Or.inl
    have he := flatExpandCentered_spec hwf hnode (by omega)
    rcases e1 : a.expandCentered root with ⟨prepId, a1⟩
    rw [e1] at he
    obtain ⟨g1, r1⟩ := he
    dsimp only at g1 r1 ⊢
    split
    · exact fun h => (g1.cap h).elim (fun h' => absurd hov h') Or.inr
    · rename_i hov1
      have hov1' : a1.overflow = 0 := by simpa using hov1
      have hb := stepCellSerial_budget g1.wf hov1' (r1 hov1') (by rw [g1.remapL4]; omega)
        (by rw [g1.remapL4]; exact hsz') (by rw [g1.masks.2]; exact hmask)
      split
      · exact fun h => Or.inr (hb h)
      · rename_i hov2
        intro h
        exact absurd (by simpa using hov2) h
  · split
    · exact Or.inl
    rename_i hK
    have hK' : k + 5 ≤ 30 := by
      rw [gt_iff_lt, u32_lt_iff, hLnat] at hK
      simp at hK
      omega
    split
    · exact Or.inl
    dsimp only
    split
    · exact fun h => absurd hov h
    · have hb := stepCellSerial_budget hwf hov hnode (by omega) hsz' hmask
      split
      · exact fun h => Or.inr (hb h)
      · rename_i hov2
        intro h
        exact absurd (by simpa using hov2) h
/--
`n` steps of the flat engine fail only when the arena had already failed or a node table is full, provided the
work stack `remapL4` has room for 26 entries and the CellNode table has at most `2 ^ 28` slots.
-/
theorem stepOneGenerationN_budget (n : ℕ) :
    ∀ {a : FlatHashLifeArena} (_ : ArenaWF a) (ox oy : Int32) (root : UInt32), 26 ≤ a.remapL4.size →
      a.remapL4.size < 2 ^ 32 → a.cellMask.toNat < 2 ^ 28 →
      (a.stepOneGenerationN n ox oy root).2.overflow ≠ 0 →
        a.overflow ≠ 0 ∨ ArenaFull (a.stepOneGenerationN n ox oy root).2 := by
  induction n with
  | zero => exact fun _ _ _ _ _ _ _ => Or.inl
  | succ n ih =>
    intro a hwf ox oy root hsz hsz' hmask
    have hb := stepOneGeneration_budget hwf ox oy root hsz hsz' hmask
    have hs := stepOneGeneration_spec hwf ox oy root
    unfold FlatHashLifeArena.stepOneGenerationN
    rcases e : a.stepOneGeneration ox oy root with ⟨⟨ox1, oy1, id1⟩, a1⟩
    rw [e] at hb hs
    obtain ⟨l1, hs1, _⟩ := hs
    dsimp only at hb l1 hs1 ⊢
    split
    · exact hb
    · rename_i hu
      have hov1 := (hs1 (by simpa using hu)).1
      intro h
      have := ih l1.wf ox1 oy1 id1 (by rw [l1.remapL4Size]; exact hsz) (by rw [l1.remapL4Size]; exact hsz')
        (by rw [l1.masks.2]; exact hmask) h
      exact this.elim (fun h' => absurd hov1 h') Or.inr

-- =========================================================================
-- One copy step
-- =========================================================================

theorem copyL4From_remapCell {src dst : FlatHashLifeArena} (hwf : ArenaWF dst) (l4Id : UInt32) (cm : Bool) :
    (dst.copyL4From src l4Id cm).2.remapCell = dst.remapCell := by
  unfold FlatHashLifeArena.copyL4From
  split
  · rfl
  · dsimp only
    split
    · rfl
    · have g := (internLevel4_spec hwf src.l4Nw[l4Id.toNat]! src.l4Ne[l4Id.toNat]! src.l4Sw[l4Id.toNat]!
        src.l4Se[l4Id.toNat]!).1
      rcases e : dst.internLevel4 src.l4Nw[l4Id.toNat]! src.l4Ne[l4Id.toNat]! src.l4Sw[l4Id.toNat]!
          src.l4Se[l4Id.toNat]! with ⟨newId, d1⟩
      rw [e] at g
      dsimp only at g ⊢
      split
      · exact g.remapCell
      · split <;> exact g.remapCell

/--
One step of the copy loop changes only the remap entry of `cellId`; when it reports no missing child and no
failure, `cellId` is remapped; and when it reports a missing child, it changed nothing and the child is an
unremapped CellNode of `src` one level below `cellId`.
-/
theorem copyCellTryStep_progress {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (hr : RemapOK src dst) (hsz : src.l4Count.toNat ≤ dst.remapL4.size)
    (hszC : src.cellCount ≤ dst.remapCell.size.toUInt32) (copyMemos : Bool) {cellId : UInt32}
    (hid : cellId < src.cellCount) :
    (∀ j : UInt32, j.toNat ≠ cellId.toNat →
      getRemapCell (copyCellTryStep dst src cellId copyMemos).2 j = getRemapCell dst j) ∧
    ((copyCellTryStep dst src cellId copyMemos).1 = UNCOMPUTED →
      (copyCellTryStep dst src cellId copyMemos).2.overflow = 0 →
      getRemapCell (copyCellTryStep dst src cellId copyMemos).2 cellId ≠ UNCOMPUTED) ∧
    ((copyCellTryStep dst src cellId copyMemos).1 ≠ UNCOMPUTED →
      (copyCellTryStep dst src cellId copyMemos).2 = dst ∧
      (copyCellTryStep dst src cellId copyMemos).1 < src.cellCount ∧
      cellLevelOf src (copyCellTryStep dst src cellId copyMemos).1 + 1 = cellLevelOf src cellId ∧
      getRemapCell dst (copyCellTryStep dst src cellId copyMemos).1 = UNCOMPUTED) := by
  obtain ⟨k, hk, hnode⟩ := NodeIs.of_lt' hsrc hid
  have hcs := hnode.children hsrc
  have hidR : cellId < dst.remapCell.size.toUInt32 := UInt32.lt_of_lt_of_le hid hszC
  have stop : ∀ d : FlatHashLifeArena, d.remapCell = dst.remapCell → d.overflow ≠ 0 →
      (∀ j : UInt32, j.toNat ≠ cellId.toNat → getRemapCell (UNCOMPUTED, d).2 j = getRemapCell dst j) ∧
      ((UNCOMPUTED, d).1 = UNCOMPUTED → (UNCOMPUTED, d).2.overflow = 0 →
        getRemapCell (UNCOMPUTED, d).2 cellId ≠ UNCOMPUTED) ∧
      ((UNCOMPUTED, d).1 ≠ UNCOMPUTED → (UNCOMPUTED, d).2 = dst ∧ (UNCOMPUTED, d).1 < src.cellCount ∧
        cellLevelOf src (UNCOMPUTED, d).1 + 1 = cellLevelOf src cellId ∧
        getRemapCell dst (UNCOMPUTED, d).1 = UNCOMPUTED) :=
    fun d hd hov => ⟨fun j _ => getRemapCell_same hd j, fun _ h => absurd h hov, fun h => absurd rfl h⟩
  have fin : ∀ d : FlatHashLifeArena, d.remapCell = dst.remapCell → ∀ newId : UInt32, newId ≠ UNCOMPUTED →
      (∀ j : UInt32, j.toNat ≠ cellId.toNat →
        getRemapCell (UNCOMPUTED, d.setRemapCell cellId newId).2 j = getRemapCell dst j) ∧
      ((UNCOMPUTED, d.setRemapCell cellId newId).1 = UNCOMPUTED →
        (UNCOMPUTED, d.setRemapCell cellId newId).2.overflow = 0 →
        getRemapCell (UNCOMPUTED, d.setRemapCell cellId newId).2 cellId ≠ UNCOMPUTED) ∧
      ((UNCOMPUTED, d.setRemapCell cellId newId).1 ≠ UNCOMPUTED →
        (UNCOMPUTED, d.setRemapCell cellId newId).2 = dst ∧
        (UNCOMPUTED, d.setRemapCell cellId newId).1 < src.cellCount ∧
        cellLevelOf src (UNCOMPUTED, d.setRemapCell cellId newId).1 + 1 = cellLevelOf src cellId ∧
        getRemapCell dst (UNCOMPUTED, d.setRemapCell cellId newId).1 = UNCOMPUTED) := by
    intro d hd newId hne
    refine ⟨fun j hj => ?_, fun _ _ => ?_, fun h => absurd rfl h⟩
    · rw [getRemapCell_set_ne (fun h => hj h.symm)]
      exact getRemapCell_same hd j
    · dsimp only
      rw [getRemapCell_set_self (by rw [hd]; exact hidR)]
      exact hne
  unfold copyCellTryStep
  dsimp only
  split
  · -- level 5
    rename_i h5
    have hk0 : k = 0 := by
      have := u8_beq_iff_toNat.mp h5
      unfold cellLevelOf at hk
      have : (5 : UInt8).toNat = 5 := rfl
      omega
    subst hk0
    obtain ⟨c1, c2, c3, c4, hM⟩ := hcs
    have s1 := copyL4From_spec hsrc hwf hr hsz copyMemos c1.lt_l4
    have q1 := copyL4From_remapCell (src := src) hwf src.cellNw[cellId.toNat]! copyMemos
    rcases e1 : dst.copyL4From src src.cellNw[cellId.toNat]! copyMemos with ⟨nw, d1⟩
    rw [e1] at s1 q1
    obtain ⟨k1, n1⟩ := s1
    have s2 := copyL4From_spec hsrc k1.wf k1.remap (by rw [k1.remapL4Size]; exact hsz) copyMemos c2.lt_l4
    have q2 := copyL4From_remapCell (src := src) k1.wf src.cellNe[cellId.toNat]! copyMemos
    rcases e2 : d1.copyL4From src src.cellNe[cellId.toNat]! copyMemos with ⟨ne, d2⟩
    rw [e2] at s2 q2
    obtain ⟨k2, n2⟩ := s2
    have k12 := k1.trans k2
    have s3 := copyL4From_spec hsrc k2.wf k2.remap (by rw [k12.remapL4Size]; exact hsz) copyMemos c3.lt_l4
    have q3 := copyL4From_remapCell (src := src) k2.wf src.cellSw[cellId.toNat]! copyMemos
    rcases e3 : d2.copyL4From src src.cellSw[cellId.toNat]! copyMemos with ⟨sw, d3⟩
    rw [e3] at s3 q3
    obtain ⟨k3, n3⟩ := s3
    have k13 := k12.trans k3
    have s4 := copyL4From_spec hsrc k3.wf k3.remap (by rw [k13.remapL4Size]; exact hsz) copyMemos c4.lt_l4
    have q4 := copyL4From_remapCell (src := src) k3.wf src.cellSe[cellId.toNat]! copyMemos
    rcases e4 : d3.copyL4From src src.cellSe[cellId.toNat]! copyMemos with ⟨se, d4⟩
    rw [e4] at s4 q4
    obtain ⟨k4, n4⟩ := s4
    have k14 := k13.trans k4
    dsimp only at n1 n2 n3 n4 k1 k2 k3 k4 q1 q2 q3 q4 ⊢
    have q14 : d4.remapCell = dst.remapCell := by rw [q4, q3, q2, q1]
    split
    · rename_i hov4
      exact stop d4 q14 (by simpa using hov4)
    · rename_i hov4
      have hov4' : d4.overflow = 0 := by simpa using hov4
      have hov3 := k4.ovf hov4'
      have hov2 := k3.ovf hov3
      have hov1 := k2.ovf hov2
      have m1 := NodeIs.extend k1.wf (k2.ext.trans (k3.ext.trans k4.ext)) (n1 hov1)
      have m2 := NodeIs.extend k2.wf (k3.ext.trans k4.ext) (n2 hov2)
      have m3 := NodeIs.extend k3.wf k4.ext (n3 hov3)
      have m4 := n4 hov4'
      have si := internCellNode_spec k14.wf (lvl := 5) (h := 0) rfl m1 m2 m3 m4
      rcases e5 : d4.internCellNode 5 nw ne sw se with ⟨newId, d5⟩
      rw [e5] at si
      obtain ⟨g5, n5⟩ := si
      have k5 := k14.trans (CopyOK.of_grows k14.wf k14.remap g5)
      dsimp only at g5 n5 k5 ⊢
      have q5 : d5.remapCell = dst.remapCell := by rw [g5.remapCell, q14]
      split
      · rename_i hov5
        exact stop d5 q5 (by simpa using hov5)
      · rename_i hov5
        have hne : newId ≠ UNCOMPUTED := (n5 (by simpa using hov5)).ne_uncomputed
        split
        · have q6 := copyL4From_remapCell (src := src) k5.wf src.cellStepRes[cellId.toNat]! copyMemos
          rcases e6 : d5.copyL4From src src.cellStepRes[cellId.toNat]! copyMemos with ⟨rr, d6⟩
          rw [e6] at q6
          dsimp only at q6 ⊢
          split
          · exact fin _ (by rw [← q5]; exact q6) newId hne
          · exact fin _ (by rw [← q5]; exact q6) newId hne
        · exact fin _ q5 newId hne
  · -- level ≥ 6
    rename_i h5
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      have : ¬ (src.cellLevel[cellId.toNat]!).toNat = (5 : UInt8).toNat := fun h => h5 (u8_beq_iff_toNat.mpr h)
      unfold cellLevelOf at hk
      have h5n : (5 : UInt8).toNat = 5 := rfl
      exact ⟨k - 1, by omega⟩
    obtain ⟨c1, c2, c3, c4, hM⟩ := hcs
    have push : ∀ (c : UInt32) (M : MacroCell), NodeIs src (j + 1) c M → getRemapCell dst c = UNCOMPUTED →
        (∀ i : UInt32, i.toNat ≠ cellId.toNat → getRemapCell (c, dst).2 i = getRemapCell dst i) ∧
        ((c, dst).1 = UNCOMPUTED → (c, dst).2.overflow = 0 → getRemapCell (c, dst).2 cellId ≠ UNCOMPUTED) ∧
        ((c, dst).1 ≠ UNCOMPUTED → (c, dst).2 = dst ∧ (c, dst).1 < src.cellCount ∧
          cellLevelOf src (c, dst).1 + 1 = cellLevelOf src cellId ∧ getRemapCell dst (c, dst).1 = UNCOMPUTED) := by
      intro c M hc hu
      refine ⟨fun _ _ => rfl, fun h => absurd h hc.ne_uncomputed, fun _ => ⟨rfl, hc.lt_cell, ?_, hu⟩⟩
      dsimp only
      rw [hc.level, hk]
    split
    · rename_i h1
      exact push _ _ c1 (by simpa using h1)
    split
    · rename_i h2
      exact push _ _ c2 (by simpa using h2)
    split
    · rename_i h3
      exact push _ _ c3 (by simpa using h3)
    split
    · rename_i h4
      exact push _ _ c4 (by simpa using h4)
    rename_i hn1 hn2 hn3 hn4
    have hmemo : src.cellStepRes[cellId.toNat]! ≠ UNCOMPUTED →
        NodeIs src (j + 1) src.cellStepRes[cellId.toNat]! (hashLifeStep (denoteCell src cellId)) := by
      intro hne
      have := hsrc.cellMemo cellId hid hne
      unfold CellMemoWF at this
      rwa [hk, show j + 1 + 5 - 5 = j + 1 by omega] at this
    have r1 := hr.child c1 (by simpa using hn1)
    have r2 := hr.child c2 (by simpa using hn2)
    have r3 := hr.child c3 (by simpa using hn3)
    have r4 := hr.child c4 (by simpa using hn4)
    have si := internCellNode_spec hwf (h := j + 1) hk r1 r2 r3 r4
    rcases e1 : dst.internCellNode src.cellLevel[cellId.toNat]! (getRemapCell dst src.cellNw[cellId.toNat]!)
        (getRemapCell dst src.cellNe[cellId.toNat]!) (getRemapCell dst src.cellSw[cellId.toNat]!)
        (getRemapCell dst src.cellSe[cellId.toNat]!) with ⟨newId, d1⟩
    rw [e1] at si
    obtain ⟨g1, n1⟩ := si
    dsimp only at g1 n1 ⊢
    cases hA : (copyMemos && src.cellStepRes[cellId.toNat]! != UNCOMPUTED)
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i hov1
        exact stop d1 g1.remapCell (by simpa using hov1)
      · rename_i hov1
        exact fin _ g1.remapCell newId (n1 (by simpa using hov1)).ne_uncomputed
    · have hA' := hA
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hA'
      simp only [Bool.true_and, ↓reduceIte]
      split
      · rename_i hrr
        exact push _ _ (hmemo hA'.2) (by simpa using hrr)
      · split
        · rename_i hov1
          exact stop d1 g1.remapCell (by simpa using hov1)
        · rename_i hov1
          exact fin (d1.setCellStepRes newId (getRemapCell dst src.cellStepRes[cellId.toNat]!)) g1.remapCell newId
            (n1 (by simpa using hov1)).ne_uncomputed

-- =========================================================================
-- The copy loop potential
-- =========================================================================

/--
Raising the set of marked elements from `p` to `q` (on a range containing a duplicate-free stack) does not raise
`2 * stackMarked - 2 * marked`: every newly marked element is counted at most once on the stack.
-/
theorem countP_pot_mono (p q : ℕ → Bool) (S : ℕ) (st : List ℕ) (hnd : st.Nodup) (hsub : ∀ x ∈ st, x < S)
    (hmono : ∀ x, x < S → p x = true → q x = true) :
    -2 * ((List.range S).countP q : ℤ) + 2 * (st.countP q : ℤ) ≤
      -2 * ((List.range S).countP p : ℤ) + 2 * (st.countP p : ℤ) := by
  have e1 := countP_split p q st (fun x hx => hmono x (hsub x hx))
  have e2 := countP_split p q (List.range S) (fun x hx => hmono x (List.mem_range.mp hx))
  have e4 := countP_le_of_nodup_subset (fun x => q x && !p x) st (List.range S) hnd
    (fun x hx => List.mem_range.mpr (hsub x hx))
  omega

/-- Whether remap slot `j` is set. -/
def remapAt (d : FlatHashLifeArena) (j : ℕ) : Bool := d.remapCell[j]! != UNCOMPUTED

/-- The CellNode ids on the copy work stack `remapCell[S ..< S + k]`. -/
def cstk (S : ℕ) (d : FlatHashLifeArena) (k : ℕ) : List ℕ := (List.range k).map fun i => (d.remapCell[S + i]!).toNat

/-- The potential of the copy loop over a source with `S` CellNodes. -/
def cpot (S : ℕ) (d : FlatHashLifeArena) (k : ℕ) : ℤ :=
  2 * (S : ℤ) - 2 * ((List.range S).countP (remapAt d) : ℤ) + 2 * ((cstk S d k).countP (remapAt d) : ℤ) - (k : ℤ)

theorem cstk_succ (S : ℕ) (d : FlatHashLifeArena) (k : ℕ) :
    cstk S d (k + 1) = cstk S d k ++ [(d.remapCell[S + k]!).toNat] := by
  simp [cstk, List.range_succ]

theorem cpot_pop {S : ℕ} {d : FlatHashLifeArena} {k : ℕ} (hm : remapAt d (d.remapCell[S + k]!).toNat = true) :
    cpot S d k = cpot S d (k + 1) - 1 := by
  unfold cpot
  rw [cstk_succ, List.countP_append]
  simp only [List.countP_cons, List.countP_nil, hm, ite_true]
  push_cast
  omega

theorem cpot_lower (S : ℕ) (d : FlatHashLifeArena) (k : ℕ) : -(k : ℤ) ≤ cpot S d k := by
  have : (List.range S).countP (remapAt d) ≤ S := by
    have := List.countP_le_length (p := remapAt d) (l := List.range S)
    simpa using this
  unfold cpot
  omega

/-- A state of the copy loop from `src` with `k` stack entries, from a root of level `L0`. -/
structure CopyState (src d : FlatHashLifeArena) (k L0 : ℕ) (root : UInt32) : Prop where
  wf : ArenaWF d
  remap : RemapOK src d
  hsz : src.l4Count.toNat ≤ d.remapL4.size
  hszC : src.cellCount.toNat + 256 ≤ d.remapCell.size
  hsz32 : d.remapCell.size < 2 ^ 32
  ovf : d.overflow = 0
  ent : ∀ i < k, d.remapCell[src.cellCount.toNat + i]! < src.cellCount ∧
    cellLevelOf src d.remapCell[src.cellCount.toNat + i]! = L0 - i
  pos : 1 ≤ k
  root : d.remapCell[src.cellCount.toNat]! = root

theorem CopyState.bound {src d : FlatHashLifeArena} (hsrc : ArenaWF src) {k L0 : ℕ} {root : UInt32}
    (h : CopyState src d k L0 root) : k + 4 ≤ L0 := by
  have h5 := cellLevelOf_ge_five hsrc (h.ent (k - 1) (by have := h.pos; omega)).1
  rw [(h.ent (k - 1) (by have := h.pos; omega)).2] at h5
  have := h.pos
  omega

theorem cstk_nodup {src d : FlatHashLifeArena} {L0 : ℕ} :
    ∀ k, (∀ i < k, cellLevelOf src d.remapCell[src.cellCount.toNat + i]! = L0 - i ∧
      5 ≤ cellLevelOf src d.remapCell[src.cellCount.toNat + i]!) → (cstk src.cellCount.toNat d k).Nodup
  | 0, _ => by simp [cstk]
  | k + 1, h => by
    rw [cstk_succ, List.nodup_append]
    refine ⟨cstk_nodup k (fun i hi => h i (by omega)), by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hxy hy
    simp only [cstk, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, he⟩ := hx
    have e : d.remapCell[src.cellCount.toNat + i]! = d.remapCell[src.cellCount.toNat + k]! := UInt32.toNat_inj.mp he
    have l1 := h i (by omega)
    have l2 := h k (by omega)
    rw [e] at l1
    omega

/-- What the copy loop guarantees about the arena `d` it returns, for the root `root` at the stack bottom. -/
def CopyGoal (d : FlatHashLifeArena) (root : UInt32) : Prop :=
  (d.overflow = 0 → remapAt d root.toNat = true) ∧ (d.overflow ≠ 0 → ArenaFull d)

/-- The copy loop meets `CopyGoal` from every state whose potential fits in `fuel`. -/
def CopyIH (src : FlatHashLifeArena) (copyMemos : Bool) (L0 : ℕ) (root fuel : UInt32) : Prop :=
  ∀ (d : FlatHashLifeArena) (sp : UInt32), CopyState src d sp.toNat L0 root →
    cpot src.cellCount.toNat d sp.toNat + L0 ≤ fuel.toNat →
    CopyGoal (d.copyCellFromLoop src copyMemos src.cellCount sp fuel) root

theorem copyCellFromLoop_overflow {src d : FlatHashLifeArena} (h : d.overflow ≠ 0) (cm : Bool)
    (base sp fuel : UInt32) : d.copyCellFromLoop src cm base sp fuel = d := by
  rw [FlatHashLifeArena.copyCellFromLoop.eq_1]
  split
  · rfl
  · simp [h]

theorem copyCellFromLoop_empty (src d : FlatHashLifeArena) (cm : Bool) (base fuel : UInt32) :
    d.copyCellFromLoop src cm base 0 fuel = d := by
  rw [FlatHashLifeArena.copyCellFromLoop.eq_1]
  split
  · rfl
  · simp

theorem getRemapCell_of_lt {d : FlatHashLifeArena} {j : UInt32} (hj : j.toNat < d.remapCell.size)
    (h32 : d.remapCell.size < 2 ^ 32) : getRemapCell d j = d.remapCell[j.toNat]! := by
  unfold getRemapCell
  rw [ite_eq_left]
  rw [u32_lt_iff]
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

theorem CopyState.nodup {src d : FlatHashLifeArena} (hsrc : ArenaWF src) {k L0 : ℕ} {root : UInt32}
    (h : CopyState src d k L0 root) : (cstk src.cellCount.toNat d k).Nodup :=
  cstk_nodup k fun i hi => ⟨(h.ent i hi).2, cellLevelOf_ge_five hsrc (h.ent i hi).1⟩

theorem CopyState.sub {src d : FlatHashLifeArena} {k L0 : ℕ} {root : UInt32} (h : CopyState src d k L0 root) :
    ∀ x ∈ cstk src.cellCount.toNat d k, x < src.cellCount.toNat := by
  intro x hx
  simp only [cstk, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact u32_lt_iff.mp (h.ent i hi).1

/-- Popping the top entry after it was remapped (or after the arena filled up). -/
theorem copy_pop {src : FlatHashLifeArena} (hsrc : ArenaWF src) {cm : Bool} {L0 : ℕ} {root fuel : UInt32}
    (ih : CopyIH src cm L0 root fuel) {d d1 : FlatHashLifeArena} {sp : UInt32}
    (hs : CopyState src d sp.toNat L0 root)
    (hfuel : cpot src.cellCount.toNat d sp.toNat + L0 ≤ fuel.toNat + 1) (k1 : CopyOK src d d1)
    (hframe : ∀ i < sp.toNat, d1.remapCell[src.cellCount.toNat + i]! = d.remapCell[src.cellCount.toNat + i]!)
    (hmono : d1.overflow = 0 → ∀ x, x < src.cellCount.toNat → remapAt d x = true → remapAt d1 x = true)
    (hm : d1.overflow = 0 → remapAt d1 (d.remapCell[src.cellCount.toNat + (sp.toNat - 1)]!).toNat = true) :
    CopyGoal (d1.copyCellFromLoop src cm src.cellCount (sp - 1) fuel) root := by
  have hpos := hs.pos
  by_cases hov : d1.overflow = 0
  · have hsp : (sp - 1).toNat = sp.toNat - 1 := u32_sub_one_toNat hs.pos
    have hstk : cstk src.cellCount.toNat d1 sp.toNat = cstk src.cellCount.toNat d sp.toNat := by
      unfold cstk
      apply List.map_congr_left
      intro i hi
      rw [hframe i (List.mem_range.mp hi)]
    have hle : cpot src.cellCount.toNat d1 sp.toNat ≤ cpot src.cellCount.toNat d sp.toNat := by
      have := countP_pot_mono (remapAt d) (remapAt d1) src.cellCount.toNat _ (hs.nodup hsrc) hs.sub (hmono hov)
      unfold cpot
      rw [hstk]
      omega
    have e : sp.toNat - 1 + 1 = sp.toNat := by omega
    have hpop := cpot_pop (S := src.cellCount.toNat) (d := d1) (k := sp.toNat - 1)
      (by rw [hframe _ (by omega)]; exact hm hov)
    rw [e] at hpop
    by_cases hk : sp.toNat - 1 = 0
    · have hsp0 : sp - 1 = 0 := u32_eq_of_toNat (by rw [hsp, hk]; rfl)
      rw [hsp0, copyCellFromLoop_empty]
      refine ⟨fun _ => ?_, fun h => absurd hov h⟩
      have := hm hov
      rw [hk, Nat.add_zero, hs.root] at this
      exact this
    · apply ih d1 (sp - 1)
      · rw [hsp]
        refine ⟨k1.wf, k1.remap, by rw [k1.remapL4Size]; exact hs.hsz, by rw [k1.remapCellSize]; exact hs.hszC,
          by rw [k1.remapCellSize]; exact hs.hsz32, hov, fun i hi => ?_, by omega, ?_⟩
        · rw [hframe i (by omega)]
          exact hs.ent i (by omega)
        · have := hframe 0 (by omega)
          rw [Nat.add_zero] at this
          rw [this]
          exact hs.root
      · rw [hsp]
        omega
  · rw [copyCellFromLoop_overflow hov]
    exact ⟨fun h => absurd h hov, fun _ => (k1.cap hov).resolve_left (fun h => h hs.ovf)⟩

/-- Pushing an unremapped child of the top entry. -/
theorem copy_push {src : FlatHashLifeArena} {cm : Bool} {L0 : ℕ} {root fuel : UInt32}
    (ih : CopyIH src cm L0 root fuel) {d : FlatHashLifeArena} {sp : UInt32}
    (hs : CopyState src d sp.toNat L0 root)
    (hfuel : cpot src.cellCount.toNat d sp.toNat + L0 ≤ fuel.toNat + 1) (hk : sp.toNat < 256) {c : UInt32}
    (hc : c < src.cellCount) (hl : cellLevelOf src c = L0 - sp.toNat) (hm : remapAt d c.toNat = false) :
    CopyGoal ((d.setRemapCell (src.cellCount + sp) c).copyCellFromLoop src cm src.cellCount (sp + 1) fuel) root := by
  have hS := hs.hszC
  have h32 := hs.hsz32
  have hpos : (src.cellCount + sp).toNat = src.cellCount.toNat + sp.toNat := u32_toNat_add (by omega)
  have k2 := CopyOK.setRemapCell hs.wf hs.remap (j := src.cellCount + sp) (v := c) (fun h => by
    exfalso
    rw [u32_lt_iff, hpos] at h
    omega)
  have hset : (d.setRemapCell (src.cellCount + sp) c).remapCell =
      d.remapCell.set! (src.cellCount.toNat + sp.toNat) c := by
    show d.remapCell.set! (src.cellCount + sp).toNat c = _
    rw [hpos]
  have hne : ∀ x, x ≠ src.cellCount.toNat + sp.toNat →
      (d.setRemapCell (src.cellCount + sp) c).remapCell[x]! = d.remapCell[x]! := by
    intro x hx
    rw [hset]
    exact getElem!_set!_ne _ _ _ _ (Ne.symm hx)
  have hsp : (sp + 1).toNat = sp.toNat + 1 := u32_toNat_add_one (by omega)
  have hcS := u32_lt_iff.mp hc
  apply ih
  · rw [hsp]
    refine ⟨k2.wf, k2.remap, by rw [k2.remapL4Size]; exact hs.hsz, by rw [k2.remapCellSize]; exact hs.hszC,
      by rw [k2.remapCellSize]; exact hs.hsz32, hs.ovf, fun i hi => ?_, by omega, ?_⟩
    · by_cases e : i = sp.toNat
      · subst e
        rw [hset, getElem!_set!_self _ _ _ (by omega)]
        exact ⟨hc, hl⟩
      · rw [hne _ (by omega)]
        exact hs.ent i (by omega)
    · rw [hne _ (by have := hs.pos; omega)]
      exact hs.root
  · rw [hsp]
    have hstk : cstk src.cellCount.toNat (d.setRemapCell (src.cellCount + sp) c) sp.toNat =
        cstk src.cellCount.toNat d sp.toNat := by
      unfold cstk
      apply List.map_congr_left
      intro i hi
      rw [hne _ (by have := List.mem_range.mp hi; omega)]
    have hrm : ∀ x, x < src.cellCount.toNat →
        remapAt (d.setRemapCell (src.cellCount + sp) c) x = remapAt d x := by
      intro x hx
      unfold remapAt
      rw [hne x (by omega)]
    have hR : (List.range src.cellCount.toNat).countP (remapAt (d.setRemapCell (src.cellCount + sp) c)) =
        (List.range src.cellCount.toNat).countP (remapAt d) :=
      List.countP_congr (fun x hx => by rw [hrm x (List.mem_range.mp hx)])
    have hT : (cstk src.cellCount.toNat d sp.toNat).countP (remapAt (d.setRemapCell (src.cellCount + sp) c)) =
        (cstk src.cellCount.toNat d sp.toNat).countP (remapAt d) :=
      List.countP_congr (fun x hx => by rw [hrm x (hs.sub x hx)])
    have htop : (d.setRemapCell (src.cellCount + sp) c).remapCell[src.cellCount.toNat + sp.toNat]! = c := by
      rw [hset, getElem!_set!_self _ _ _ (by omega)]
    unfold cpot
    rw [cstk_succ, List.countP_append, hstk, hT, hR, htop]
    simp only [List.countP_cons, List.countP_nil, hrm _ hcS, hm]
    unfold cpot at hfuel
    push_cast
    omega

theorem nat_toUInt32_toNat {x : ℕ} (h : x < 2 ^ 32) : x.toUInt32.toNat = x := by
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

/--
The copy loop runs out of neither step budget nor stack space: started on a root of level `L0` with enough
`fuel` for the potential, it either remaps the root or stops because a node table is full.
-/
theorem copyCellFromLoop_budget {src : FlatHashLifeArena} (hsrc : ArenaWF src) (cm : Bool) (L0 : ℕ)
    (root : UInt32) (n : ℕ) : ∀ fuel : UInt32, fuel.toNat ≤ n → CopyIH src cm L0 root fuel := by
  induction n with
  | zero =>
    intro fuel hn d sp hs hfuel
    exfalso
    have := cpot_lower src.cellCount.toNat d sp.toNat
    have := hs.bound hsrc
    omega
  | succ n ih =>
    intro fuel hn d sp hs hfuel
    have hf : fuel ≠ 0 := by
      intro h
      subst h
      have := cpot_lower src.cellCount.toNat d sp.toNat
      have := hs.bound hsrc
      simp at hfuel
      omega
    have hf0 : fuel.toNat ≠ 0 := fun h => hf (u32_eq_of_toNat (by simpa using h))
    have hf1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub_one_toNat (by omega)
    have hfuel' : cpot src.cellCount.toNat d sp.toNat + L0 ≤ (fuel - 1).toNat + 1 := by
      rw [hf1]
      omega
    have ih' := ih (fuel - 1) (by omega)
    rw [FlatHashLifeArena.copyCellFromLoop.eq_1]
    simp only [hf, dite_false]
    have hpos := hs.pos
    have hsp0 : sp ≠ 0 := fun h => by
      subst h
      simp at hpos
    have hcond : (sp == 0 || d.overflow != 0) = false := by simp [hsp0, hs.ovf]
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    have hb := hs.bound hsrc
    have hS := hs.hszC
    have h32 := hs.hsz32
    obtain ⟨hidS, hlev⟩ := hs.ent (sp.toNat - 1) (by omega)
    have hL0 : L0 < 256 := by
      have h0 := (hs.ent 0 (by omega)).2
      have := u8_toNat_lt (src.cellLevel[(d.remapCell[src.cellCount.toNat + 0]!).toNat]!)
      unfold cellLevelOf at h0
      omega
    have htp : (src.cellCount + sp - 1).toNat = src.cellCount.toNat + (sp.toNat - 1) := by
      rw [u32_sub_one_toNat (by rw [u32_toNat_add (by omega)]; omega), u32_toNat_add (by omega)]
      omega
    have htop : getRemapCell d (src.cellCount + sp - 1) = d.remapCell[src.cellCount.toNat + (sp.toNat - 1)]! := by
      rw [getRemapCell_of_lt (by rw [htp]; omega) h32, htp]
    rw [htop]
    rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hidS; omega)]
    generalize hcid : d.remapCell[src.cellCount.toNat + (sp.toNat - 1)]! = cid at hidS hlev ⊢
    have hcS := u32_lt_iff.mp hidS
    have hcidR : getRemapCell d cid = d.remapCell[cid.toNat]! := getRemapCell_of_lt (by omega) h32
    split
    · rename_i hrm
      exact copy_pop hsrc ih' hs hfuel' (CopyOK.refl hs.wf hs.remap) (fun _ _ => rfl) (fun _ _ _ h => h)
        (fun _ => by rw [hcid]; simpa [remapAt, hcidR] using hrm)
    · rename_i hun
      have hszC' : src.cellCount ≤ d.remapCell.size.toUInt32 := by
        rw [u32_le_iff, nat_toUInt32_toNat h32]
        omega
      have k1 := copyCellTryStep_spec hsrc hs.wf hs.remap hs.hsz hszC' cm hidS
      have pr := copyCellTryStep_progress hsrc hs.wf hs.remap hs.hsz hszC' cm hidS
      rcases e : copyCellTryStep d src cid cm with ⟨missing, d1⟩
      rw [e] at k1 pr
      obtain ⟨fr, pg, pu⟩ := pr
      dsimp only at k1 fr pg pu ⊢
      have hsz1 := k1.remapCellSize
      have hfr : ∀ x, x < d.remapCell.size → x ≠ cid.toNat → d1.remapCell[x]! = d.remapCell[x]! := by
        intro x hx hne
        have := fr x.toUInt32 (by rw [nat_toUInt32_toNat (by omega)]; exact hne)
        rw [getRemapCell_of_lt (by rw [nat_toUInt32_toNat (by omega)]; omega) (by omega),
          getRemapCell_of_lt (by rw [nat_toUInt32_toNat (by omega)]; omega) h32,
          nat_toUInt32_toNat (by omega)] at this
        exact this
      have hframe : ∀ i < sp.toNat,
          d1.remapCell[src.cellCount.toNat + i]! = d.remapCell[src.cellCount.toNat + i]! :=
        fun i hi => hfr _ (by omega) (by omega)
      have hdone : d1.overflow = 0 → missing = UNCOMPUTED → remapAt d1 cid.toNat = true := by
        intro hov hm
        have := pg hm hov
        rw [getRemapCell_of_lt (by omega) (by omega)] at this
        simpa [remapAt] using this
      split
      · rename_i hov
        have hov' : d1.overflow ≠ 0 := by simpa using hov
        rw [copyCellFromLoop_empty]
        exact ⟨fun h => absurd h hov', fun _ => (k1.cap hov').resolve_left (fun h => h hs.ovf)⟩
      · rename_i hov
        have hov' : d1.overflow = 0 := by simpa using hov
        split
        · rename_i hmiss
          have hmiss' : missing = UNCOMPUTED := by simpa using hmiss
          refine copy_pop hsrc ih' hs hfuel' k1 hframe (fun _ x hx hr => ?_) (fun _ => by
            rw [hcid]
            exact hdone hov' hmiss')
          by_cases hx' : x = cid.toNat
          · subst hx'
            exact hdone hov' hmiss'
          · unfold remapAt at hr ⊢
            rw [hfr x (by omega) hx']
            exact hr
        · rename_i hmiss
          have hmiss' : missing ≠ UNCOMPUTED := by simpa using hmiss
          obtain ⟨hd1, hlt, hlv, hu⟩ := pu hmiss'
          subst hd1
          split
          · rename_i hdepth
            exfalso
            rw [ge_iff_le, u32_le_iff] at hdepth
            have : copyStackDepth.toNat = 256 := rfl
            omega
          · have hmS := u32_lt_iff.mp hlt
            refine copy_push ih' hs hfuel' (by omega) hlt (by omega) ?_
            rw [getRemapCell_of_lt (by omega) h32] at hu
            simp [remapAt, hu]

/--
`copySubgraphInto` remaps a valid root of `src` unless a node table of the destination fills up, provided the
destination has the scratch space (`canCopySubgraphFrom`) and the source has at most `2 ^ 29` CellNodes (so
the step budget `(cellCount + 1) * 6 + 256` does not wrap around).
-/
theorem copySubgraphInto_budget {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (hov : dst.overflow = 0) (hcan : dst.canCopySubgraphFrom src = true) {rootId : UInt32}
    (hid : rootId < src.cellCount) (hS : src.cellCount.toNat < 2 ^ 29) (h32 : dst.remapCell.size < 2 ^ 32)
    (copyMemos : Bool) : CopyGoal (copySubgraphInto dst src rootId copyMemos) rootId := by
  unfold copySubgraphInto
  rw [ite_eq_right (by simp [hcan])]
  simp only [FlatHashLifeArena.canCopySubgraphFrom, Bool.and_eq_true, decide_eq_true_eq] at hcan
  obtain ⟨⟨hl4, hst⟩, hcells⟩ := hcan
  rw [ge_iff_le] at hst
  rw [u32_le_iff] at hl4 hst hcells
  have hs1 := toUInt32_toNat_le dst.remapL4.size
  have hs2 : dst.remapCell.size.toUInt32.toNat = dst.remapCell.size := nat_toUInt32_toNat h32
  have h256 : copyStackDepth.toNat = 256 := rfl
  rw [u32_toNat_sub (by omega), h256] at hcells
  obtain ⟨w1, s1, o1, c1, z1, e1⟩ := initRemapL4Loop_spec src.l4Count _ dst 0 (Nat.le_refl _) hwf (by omega)
  obtain ⟨w2, s2, o2, c2, z2, e2⟩ := initRemapCellLoop_spec src.cellCount _ (dst.initRemapL4Loop 0 src.l4Count) 0
    (Nat.le_refl _) w1 (by rw [c1]; omega)
  have hszC : src.cellCount ≤
      ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount).remapCell.size.toUInt32 := by
    rw [z2, c1, u32_le_iff]
    omega
  have hr2 : RemapOK src ((dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount) := by
    refine RemapOK.init hsrc w2 (fun j hj => ?_) (fun j hj => ?_) hszC
    · rw [c2, e1 j hj]
      simp
    · rw [e2 j hj]
      simp
  dsimp only
  rw [ite_eq_right (by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hid; omega)]
  generalize hd2 : (dst.initRemapL4Loop 0 src.l4Count).initRemapCellLoop 0 src.cellCount = d2 at w2 hszC hr2 z2 o2 c2
  have hsz2 : d2.remapCell.size = dst.remapCell.size := by rw [z2, c1]
  have k3 := CopyOK.setRemapCell w2 hr2 (j := src.cellCount) (v := rootId)
    (fun h => absurd h (UInt32.lt_irrefl _))
  have hset : (d2.setRemapCell src.cellCount rootId).remapCell[src.cellCount.toNat]! = rootId :=
    getElem!_set!_self _ _ _ (by omega)
  have hidN := u32_lt_iff.mp hid
  have hL0 : cellLevelOf src rootId < 256 := by
    have := u8_toNat_lt (src.cellLevel[rootId.toNat]!)
    unfold cellLevelOf
    omega
  have hs3 : CopyState src (d2.setRemapCell src.cellCount rootId) (UInt32.toNat 1) (cellLevelOf src rootId)
      rootId := by
    refine ⟨k3.wf, k3.remap, by rw [k3.remapL4Size, c2, z1]; omega, by rw [k3.remapCellSize]; omega,
      by rw [k3.remapCellSize]; omega, by show d2.overflow = 0; rw [o2, o1]; exact hov, fun i hi => ?_, by decide, hset⟩
    simp only [UInt32.reduceToNat] at hi
    obtain rfl : i = 0 := by omega
    rw [Nat.add_zero, hset]
    exact ⟨hid, by omega⟩
  have hfuel : ((src.cellCount + 1) * 6 + 256).toNat = (src.cellCount.toNat + 1) * 6 + 256 := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.reduceToNat]
    omega
  have hpot : cpot src.cellCount.toNat (d2.setRemapCell src.cellCount rootId) (UInt32.toNat 1) +
      ((cellLevelOf src rootId : ℕ) : ℤ) ≤ (((src.cellCount + 1) * 6 + 256).toNat : ℤ) := by
    rw [hfuel]
    have h1 := List.countP_le_length (p := remapAt (d2.setRemapCell src.cellCount rootId))
      (l := cstk src.cellCount.toNat (d2.setRemapCell src.cellCount rootId) (UInt32.toNat 1))
    have h2 := List.countP_le_length (p := remapAt (d2.setRemapCell src.cellCount rootId))
      (l := List.range src.cellCount.toNat)
    have hl1 : (cstk src.cellCount.toNat (d2.setRemapCell src.cellCount rootId) (UInt32.toNat 1)).length = 1 := by
      simp [cstk]
    rw [hl1] at h1
    rw [List.length_range] at h2
    unfold cpot
    omega
  exact copyCellFromLoop_budget hsrc copyMemos _ rootId _ _ (Nat.le_refl _) _ 1 hs3 hpot

/--
`copySubgraphFrom` fails only when a node table of the destination is full, for a valid root of `src`, a
non-failed destination with the scratch space to copy from `src`, and a source with at most `2 ^ 29` CellNodes.
-/
theorem copySubgraphFrom_budget {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    (hov : dst.overflow = 0) (hcan : dst.canCopySubgraphFrom src = true) {rootId : UInt32}
    (hid : rootId < src.cellCount) (hS : src.cellCount.toNat < 2 ^ 29) (h32 : dst.remapCell.size < 2 ^ 32)
    (copyMemos : Bool) :
    (dst.copySubgraphFrom src rootId copyMemos).2.overflow ≠ 0 →
      ArenaFull (dst.copySubgraphFrom src rootId copyMemos).2 := by
  have G := copySubgraphInto_budget hsrc hwf hov hcan hid hS h32 copyMemos
  have sc := (copySubgraphInto_spec hsrc hwf rootId copyMemos).1
  have hcan' := hcan
  simp only [FlatHashLifeArena.canCopySubgraphFrom, Bool.and_eq_true, decide_eq_true_eq] at hcan'
  have hcells := hcan'.2
  rw [u32_le_iff, u32_toNat_sub (by rw [ge_iff_le] at hcan'; exact hcan'.1.2)] at hcells
  have hs2 : dst.remapCell.size.toUInt32.toNat = dst.remapCell.size := nat_toUInt32_toNat h32
  have h256 : copyStackDepth.toNat = 256 := rfl
  rw [hs2, h256] at hcells
  unfold FlatHashLifeArena.copySubgraphFrom
  generalize copySubgraphInto dst src rootId copyMemos = d1 at G sc ⊢
  dsimp only
  have hroot : ¬ (rootId ≥ src.cellCount) := by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hid; omega
  simp only [hroot, ↓reduceIte]
  have hidN := u32_lt_iff.mp hid
  split
  · rename_i hc
    intro _
    show ArenaFull d1
    by_cases ho : d1.overflow = 0
    · exfalso
      have hm := G.1 ho
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      unfold getOverflow at hc
      rcases hc with hc | hc
      · exact hc ho
      · rw [getRemapCell_of_lt (by rw [sc.remapCellSize]; omega) (by rw [sc.remapCellSize]; exact h32)] at hc
        simp [remapAt, hc] at hm
    · exact G.2 ho
  · rename_i hc
    intro h'
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_or, Decidable.not_not] at hc
    unfold getOverflow at hc
    exact absurd hc.1 h'

/--
`compactRootFrom` fails only when a node table of the destination is full, for a valid root of a non-failed
`src`, a destination with the scratch space to copy from `src`, and a source with at most `2 ^ 29` CellNodes.
(The fallback copy clears the destination's failure flag first, so the destination may have failed before.)
-/
theorem compactRootFrom_budget {src dst : FlatHashLifeArena} (hsrc : ArenaWF src) (hwf : ArenaWF dst)
    {rootId : UInt32} (hid : rootId < src.cellCount) (hso : src.overflow = 0)
    (hcan : dst.canCopySubgraphFrom src = true) (hS : src.cellCount.toNat < 2 ^ 29)
    (h32 : dst.remapCell.size < 2 ^ 32) :
    (dst.compactRootFrom src rootId).1.1 = UNCOMPUTED → ArenaFull (dst.compactRootFrom src rootId).2 := by
  unfold FlatHashLifeArena.compactRootFrom
  rw [ite_eq_right (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
    exact ⟨by rw [ge_iff_le, u32_le_iff]; have := u32_lt_iff.mp hid; omega, hso⟩)]
  obtain ⟨sc1, hi1, _⟩ := copySubgraphFrom_spec hsrc hwf rootId true
  rcases e1 : dst.copySubgraphFrom src rootId true with ⟨id1, d1⟩
  rw [e1] at sc1 hi1
  dsimp only at sc1 hi1 ⊢
  split
  · rename_i hov1
    exact fun h => absurd h (hi1.mpr (by simpa using hov1))
  · have w2 := sc1.wf.clearOverflow
    have hcan2 : d1.clearOverflow.canCopySubgraphFrom src = true := by
      have e : d1.clearOverflow.canCopySubgraphFrom src = dst.canCopySubgraphFrom src := by
        unfold FlatHashLifeArena.canCopySubgraphFrom
        show (decide (src.l4Count ≤ d1.remapL4.size.toUInt32) &&
          decide (d1.remapCell.size.toUInt32 ≥ copyStackDepth) &&
          decide (src.cellCount ≤ d1.remapCell.size.toUInt32 - copyStackDepth)) = _
        rw [sc1.remapL4Size, sc1.remapCellSize]
      rw [e]
      exact hcan
    have h32' : d1.clearOverflow.remapCell.size < 2 ^ 32 := by
      show d1.remapCell.size < _
      rw [sc1.remapCellSize]
      exact h32
    have hb := copySubgraphFrom_budget hsrc w2 rfl hcan2 hid hS h32' false
    obtain ⟨_, hi3, _⟩ := copySubgraphFrom_spec hsrc w2 rootId false
    rcases e3 : d1.clearOverflow.copySubgraphFrom src rootId false with ⟨id2, d3⟩
    rw [e3] at hb hi3
    dsimp only at hb hi3 ⊢
    intro h
    exact hb (fun h0 => hi3.mpr h0 h)

end Algorithm

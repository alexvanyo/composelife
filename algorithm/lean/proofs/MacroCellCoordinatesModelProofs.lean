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

import proofs.MacroCellQueryProofs
import models.MacroCellCoordinatesModel
import models.HashLifeComputationModel

namespace Algorithm.KotlinModel

/-! ## `cellToLeafBit` -/

private theorem int32_toUInt32_of_nonneg (x : Int32) (h0 : 0 ≤ x.toInt) :
    x.toUInt32 = x.toInt.toNat.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [Int32.toNat_toUInt32_of_le (Int32.le_iff_toInt_le.mpr (by simpa using h0))]
  have := Int32.toNatClampNeg_lt x
  simp
  omega

/-- What a successful `cellToLeafBitModel` call returns: the Morton index of an in-range coordinate. -/
private theorem cellToLeafBitModel_eq_some {x y : Int32} {b : UInt32} (h : cellToLeafBitModel x y = some b) :
    (0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) ∧
      b.toNat = Algorithm.mortonIndex x.toInt.toNat y.toInt.toNat := by
  unfold cellToLeafBitModel at h
  split at h
  · rename_i hr
    cases h
    refine ⟨hr, ?_⟩
    rw [int32_toUInt32_of_nonneg x hr.1, int32_toUInt32_of_nonneg y hr.2.2.1]
    exact Algorithm.cellToLeafBit_morton _ (by omega) _ (by omega)
  · cases h

theorem cellToLeafBitModel_some_iff_Impl (x y : Int32) :
    (cellToLeafBitModel x y).isSome ↔
      (0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) := by
  unfold cellToLeafBitModel
  split <;> simp_all

theorem cellToLeafBitModel_lt64_Impl (x y : Int32) (b : UInt32)
    (h : cellToLeafBitModel x y = some b) :
    b.toNat < 64 := by
  obtain ⟨hr, hb⟩ := cellToLeafBitModel_eq_some h
  rw [hb]
  exact Algorithm.mortonIndex_lt_64 _ (by omega) _ (by omega)

theorem cellToLeafBitModel_eq_morton_Impl (x y : Int32) (b : UInt32)
    (h : cellToLeafBitModel x y = some b) :
    b.toNat = Algorithm.mortonIndex x.toInt.toNat y.toInt.toNat :=
  (cellToLeafBitModel_eq_some h).2

theorem cellToLeafBitModel_inj_Impl (x1 y1 x2 y2 : Int32) (b : UInt32)
    (h1 : cellToLeafBitModel x1 y1 = some b)
    (h2 : cellToLeafBitModel x2 y2 = some b) :
    x1 = x2 ∧ y1 = y2 := by
  obtain ⟨hr1, hb1⟩ := cellToLeafBitModel_eq_some h1
  obtain ⟨hr2, hb2⟩ := cellToLeafBitModel_eq_some h2
  have hinj := Algorithm.mortonIndex_inj (by omega) (by omega) (by omega) (by omega) (hb1.symm.trans hb2)
  exact ⟨Int32.toInt_inj.mp (by omega), Int32.toInt_inj.mp (by omega)⟩

/-! ## `coordinatesToLeaf` -/

/-- The bit that one coordinate contributes to `coordinatesToLeafModel`. -/
private def leafBitMask (ox oy : Int32) (p : Int32 × Int32) : UInt64 :=
  match cellToLeafBitModel (p.1 - ox) (p.2 - oy) with
  | some bit => (1 : UInt64) <<< bit.toUInt64
  | none => 0

private theorem coordinatesToLeafModel_eq_fold (coords : List (Int32 × Int32)) (ox oy : Int32) :
    coordinatesToLeafModel coords ox oy = coords.foldl (fun a p => a ||| leafBitMask ox oy p) 0 := by
  unfold coordinatesToLeafModel
  congr
  funext a p
  unfold leafBitMask
  dsimp only
  cases cellToLeafBitModel (p.1 - ox) (p.2 - oy)
  · exact UInt64.or_zero.symm
  · rfl

private theorem foldl_or_acc (g : Int32 × Int32 → UInt64) (acc : UInt64) (coords : List (Int32 × Int32)) :
    coords.foldl (fun a p => a ||| g p) acc = acc ||| coords.foldl (fun a p => a ||| g p) 0 := by
  induction coords generalizing acc with
  | nil => exact UInt64.or_zero.symm
  | cons p ps ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 ||| g p), UInt64.zero_or, UInt64.or_assoc]

theorem coordinatesToLeafModel_empty_Impl (ox oy : Int32) :
    coordinatesToLeafModel [] ox oy = 0 := rfl

theorem coordinatesToLeafModel_append_Impl (xs ys : List (Int32 × Int32)) (ox oy : Int32) :
    coordinatesToLeafModel (xs ++ ys) ox oy =
      coordinatesToLeafModel xs ox oy ||| coordinatesToLeafModel ys ox oy := by
  rw [coordinatesToLeafModel_eq_fold, coordinatesToLeafModel_eq_fold, coordinatesToLeafModel_eq_fold,
    List.foldl_append, foldl_or_acc]

/-- Bit `i` of `coordinatesToLeafModel` is set exactly when some coordinate maps to bit `i`. -/
private theorem coordinatesToLeafModel_getLsbD (coords : List (Int32 × Int32)) (ox oy : Int32) (i : Nat) :
    (coordinatesToLeafModel coords ox oy).toBitVec.getLsbD i = true ↔
      ∃ p ∈ coords, ∃ b, cellToLeafBitModel (p.1 - ox) (p.2 - oy) = some b ∧ b.toNat = i := by
  induction coords with
  | nil => simp [coordinatesToLeafModel]
  | cons p ps ih =>
    rw [show p :: ps = [p] ++ ps from rfl, coordinatesToLeafModel_append_Impl, UInt64.toBitVec_or,
      BitVec.getLsbD_or, Bool.or_eq_true, ih, coordinatesToLeafModel_eq_fold]
    simp only [List.mem_append, List.mem_singleton, exists_eq_or_imp, List.foldl_cons, List.foldl_nil,
      UInt64.zero_or]
    unfold leafBitMask
    cases hb : cellToLeafBitModel (p.1 - ox) (p.2 - oy) with
    | none => simp
    | some b =>
      have hlt : b.toUInt64.toNat < 64 := by
        rw [UInt32.toNat_toUInt64]; exact cellToLeafBitModel_lt64_Impl _ _ b hb
      simp only [Algorithm.getLsbD_one_shl _ hlt, UInt32.toNat_toUInt64, Option.some.injEq,
        exists_eq_left']
      constructor
      · rintro (h | h)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          exact Or.inl h.2.symm
        · exact Or.inr h
      · rintro (h | h)
        · have := cellToLeafBitModel_lt64_Impl _ _ b hb
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact Or.inl ⟨by omega, h.symm⟩
        · exact Or.inr h

/-! ## `leafToCoordinates` -/

private theorem and_one_ne_zero (v : UInt64) : ((v &&& 1) != 0) = ((v &&& 1) == 1) := by
  have h : (v &&& 1).toNat < 2 := by
    rw [UInt64.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases (by omega : (v &&& 1).toNat = 0 ∨ (v &&& 1).toNat = 1) with h0 | h1
  · rw [UInt64.toNat_inj.mp (h0.trans UInt64.toNat_zero.symm)]; decide
  · rw [UInt64.toNat_inj.mp (h1.trans UInt64.toNat_one.symm)]; decide

/-- `leafToCoordinatesModel` lists the in-window cells whose Morton bit is set, offset by `(ox, oy)`. -/
theorem mem_leafToCoordinatesModel_iff_Impl (leaf : UInt64) (ox oy : Int32) (p : Int32 × Int32) :
    p ∈ leafToCoordinatesModel leaf ox oy ↔
      ∃ nx < 8, ∃ ny < 8, leaf.toBitVec.getLsbD (Algorithm.mortonIndex nx ny) = true ∧
        p = (Int32.ofInt (nx : Int) + ox, Int32.ofInt (ny : Int) + oy) := by
  unfold leafToCoordinatesModel
  by_cases hzero : leaf = 0
  · subst hzero
    simp
  · simp only [beq_false_of_ne hzero, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range,
      List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨ny, hy, nx, hx, hbit, rfl⟩
      refine ⟨nx, hx, ny, hy, ?_, rfl⟩
      have hb := Algorithm.cellToLeafBit_morton nx hx ny hy
      simp only [Nat.toUInt32_eq] at hb
      rw [and_one_ne_zero, Algorithm.shr_and_one_eq_one _ _ (by
        rw [UInt32.toNat_toUInt64, hb]; exact Algorithm.mortonIndex_lt_64 _ hx _ hy),
        UInt32.toNat_toUInt64, hb] at hbit
      exact hbit
    · rintro ⟨nx, hx, ny, hy, hbit, rfl⟩
      refine ⟨ny, hy, nx, hx, ?_, rfl⟩
      have hb := Algorithm.cellToLeafBit_morton nx hx ny hy
      simp only [Nat.toUInt32_eq] at hb
      rw [and_one_ne_zero, Algorithm.shr_and_one_eq_one _ _ (by
        rw [UInt32.toNat_toUInt64, hb]; exact Algorithm.mortonIndex_lt_64 _ hx _ hy),
        UInt32.toNat_toUInt64, hb]
      exact hbit

private theorem toInt_ofInt_nat_lt8 {n : Nat} (h : n < 8) : (Int32.ofInt (n : Int)).toInt = n :=
  Int32.toInt_ofInt_of_le (by omega) (by omega)

private theorem mortonIndex_surj : ∀ i < 64, ∃ x < 8, ∃ y < 8, Algorithm.mortonIndex x y = i := by
  decide

theorem coordinatesToLeaf_leafToCoordinates_Impl (leaf : UInt64) (ox oy : Int32) :
    coordinatesToLeafModel (leafToCoordinatesModel leaf ox oy) ox oy = leaf := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64
  apply Bool.eq_iff_iff.mpr
  rw [coordinatesToLeafModel_getLsbD]
  simp only [mem_leafToCoordinatesModel_iff_Impl]
  constructor
  · rintro ⟨_, ⟨nx, hx, ny, hy, hbit, rfl⟩, b, hcb, rfl⟩
    rw [Int32.add_sub_cancel, Int32.add_sub_cancel] at hcb
    rw [cellToLeafBitModel_eq_morton_Impl _ _ b hcb, toInt_ofInt_nat_lt8 hx, toInt_ofInt_nat_lt8 hy]
    exact hbit
  · intro hleaf
    obtain ⟨nx, hx, ny, hy, rfl⟩ := mortonIndex_surj i hi64
    have hsome : (cellToLeafBitModel (Int32.ofInt (nx : Int)) (Int32.ofInt (ny : Int))).isSome := by
      rw [cellToLeafBitModel_some_iff_Impl, toInt_ofInt_nat_lt8 hx, toInt_ofInt_nat_lt8 hy]
      omega
    obtain ⟨b, hcb⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨_, ⟨nx, hx, ny, hy, hleaf, rfl⟩, b, ?_, ?_⟩
    · rw [Int32.add_sub_cancel, Int32.add_sub_cancel]
      exact hcb
    · rw [cellToLeafBitModel_eq_morton_Impl _ _ b hcb, toInt_ofInt_nat_lt8 hx, toInt_ofInt_nat_lt8 hy]
      rfl

theorem leafToCoordinates_coordinatesToLeaf_Impl (coords : List (Int32 × Int32)) (ox oy : Int32)
    (p : Int32 × Int32) :
    p ∈ leafToCoordinatesModel (coordinatesToLeafModel coords ox oy) ox oy ↔
      p ∈ coords ∧ (cellToLeafBitModel (p.1 - ox) (p.2 - oy)).isSome := by
  rw [mem_leafToCoordinatesModel_iff_Impl]
  constructor
  · rintro ⟨nx, hx, ny, hy, hbit, rfl⟩
    obtain ⟨q, hq, b, hcb, hbi⟩ := (coordinatesToLeafModel_getLsbD coords ox oy _).mp hbit
    obtain ⟨hr, hb⟩ := cellToLeafBitModel_eq_some hcb
    have hinj := Algorithm.mortonIndex_inj (by omega) (by omega) hx hy (hb.symm.trans hbi)
    have hqx : q.1 - ox = Int32.ofInt (nx : Int) :=
      Int32.toInt_inj.mp (by rw [toInt_ofInt_nat_lt8 hx]; omega)
    have hqy : q.2 - oy = Int32.ofInt (ny : Int) :=
      Int32.toInt_inj.mp (by rw [toInt_ofInt_nat_lt8 hy]; omega)
    have hq' : q = (Int32.ofInt (nx : Int) + ox, Int32.ofInt (ny : Int) + oy) := by
      rw [← hqx, ← hqy, Int32.sub_add_cancel, Int32.sub_add_cancel]
    subst hq'
    refine ⟨hq, ?_⟩
    rw [Int32.add_sub_cancel, Int32.add_sub_cancel]
    exact Option.isSome_iff_exists.mpr ⟨b, by rw [Int32.add_sub_cancel, Int32.add_sub_cancel] at hcb; exact hcb⟩
  · rintro ⟨hp, hsome⟩
    obtain ⟨b, hcb⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hr, hb⟩ := cellToLeafBitModel_eq_some hcb
    refine ⟨(p.1 - ox).toInt.toNat, by omega, (p.2 - oy).toInt.toNat, by omega, ?_, ?_⟩
    · exact (coordinatesToLeafModel_getLsbD coords ox oy _).mpr ⟨p, hp, b, hcb, hb⟩
    · have hx : Int32.ofInt ((p.1 - ox).toInt.toNat : Int) = p.1 - ox :=
        Int32.toInt_inj.mp (by rw [toInt_ofInt_nat_lt8 (by omega)]; omega)
      have hy : Int32.ofInt ((p.2 - oy).toInt.toNat : Int) = p.2 - oy :=
        Int32.toInt_inj.mp (by rw [toInt_ofInt_nat_lt8 (by omega)]; omega)
      rw [hx, hy, Int32.sub_add_cancel, Int32.sub_add_cancel]

/-! ## Cells of the encoded leaves -/

private theorem toInt_ofInt_of_lt8 {x : Int} (h0 : 0 ≤ x) (h8 : x < 8) : (Int32.ofInt x).toInt = x :=
  Int32.toInt_ofInt_of_le (by omega) (by omega)

theorem leafAt_coordinatesToLeafModel_Impl (coords : List (Int32 × Int32)) (ox oy : Int32) (x y : Int)
    (hx : 0 ≤ x ∧ x < 8) (hy : 0 ≤ y ∧ y < 8) :
    Algorithm.leafAt (coordinatesToLeafModel coords ox oy) x y =
      decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords) := by
  unfold Algorithm.leafAt
  rw [ite_eq_left ⟨hx.1, hx.2, hy.1, hy.2⟩, Bool.eq_iff_iff, decide_eq_true_eq, coordinatesToLeafModel_getLsbD]
  constructor
  · rintro ⟨p, hp, b, hcb, hbi⟩
    obtain ⟨hr, hb⟩ := cellToLeafBitModel_eq_some hcb
    have hinj := Algorithm.mortonIndex_inj (by omega) (by omega) (by omega) (by omega) (hb.symm.trans hbi)
    have hpx : p.1 - ox = Int32.ofInt x := Int32.toInt_inj.mp (by rw [toInt_ofInt_of_lt8 hx.1 hx.2]; omega)
    have hpy : p.2 - oy = Int32.ofInt y := Int32.toInt_inj.mp (by rw [toInt_ofInt_of_lt8 hy.1 hy.2]; omega)
    have hp' : p = (ox + Int32.ofInt x, oy + Int32.ofInt y) := by
      rw [← hpx, ← hpy, Int32.add_comm ox, Int32.add_comm oy, Int32.sub_add_cancel, Int32.sub_add_cancel]
    exact hp' ▸ hp
  · intro hp
    have hsub : ∀ a b : Int32, a + b - a = b := fun a b => by rw [Int32.add_comm, Int32.add_sub_cancel]
    have hsome : (cellToLeafBitModel (Int32.ofInt x) (Int32.ofInt y)).isSome := by
      rw [cellToLeafBitModel_some_iff_Impl, toInt_ofInt_of_lt8 hx.1 hx.2, toInt_ofInt_of_lt8 hy.1 hy.2]
      omega
    obtain ⟨b, hcb⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨_, hp, b, by rw [hsub, hsub]; exact hcb, ?_⟩
    rw [cellToLeafBitModel_eq_morton_Impl _ _ b hcb, toInt_ofInt_of_lt8 hx.1 hx.2, toInt_ofInt_of_lt8 hy.1 hy.2]

private theorem shift8 (o : Int32) (x : Int) : o + 8 + Int32.ofInt (x - 8) = o + Int32.ofInt x := by
  rw [Int.sub_eq_add_neg, Int32.ofInt_add, Int32.add_assoc, ← Int32.add_assoc 8, Int32.add_comm 8,
    Int32.add_assoc, show (8 : Int32) + Int32.ofInt (-8) = 0 by decide, Int32.add_zero]

theorem level4CellAt_coordinatesToLevel4Model_Impl (coords : List (Int32 × Int32)) (ox oy : Int32) (x y : Int)
    (hx : 0 ≤ x ∧ x < 16) (hy : 0 ≤ y ∧ y < 16) :
    level4CellAt (coordinatesToLevel4Model coords ox oy).nw (coordinatesToLevel4Model coords ox oy).ne
        (coordinatesToLevel4Model coords ox oy).sw (coordinatesToLevel4Model coords ox oy).se x y =
      decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords) := by
  unfold level4CellAt coordinatesToLevel4Model
  rw [ite_eq_right (by omega)]
  by_cases hx8 : x < 8 <;> by_cases hy8 : y < 8 <;> simp only [hx8, hy8, ↓reduceIte]
  · exact leafAt_coordinatesToLeafModel_Impl coords ox oy x y ⟨hx.1, hx8⟩ ⟨hy.1, hy8⟩
  · rw [leafAt_coordinatesToLeafModel_Impl coords ox (oy + 8) x (y - 8) ⟨hx.1, hx8⟩ (by omega), shift8]
  · rw [leafAt_coordinatesToLeafModel_Impl coords (ox + 8) oy (x - 8) y (by omega) ⟨hy.1, hy8⟩, shift8]
  · rw [leafAt_coordinatesToLeafModel_Impl coords (ox + 8) (oy + 8) (x - 8) (y - 8) (by omega) (by omega),
      shift8, shift8]

end Algorithm.KotlinModel

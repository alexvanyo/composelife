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

import proofs.GeometryExtensionsModelProofs

namespace Geometry.KotlinModel

/-- Signed Chebyshev distance equals `max |x| |y|` when `x, y ≠ Int32.minValue`. -/
theorem chebyshevDistanceModel_eq_natMax (p : UInt64)
    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue) :
    (chebyshevDistanceModel p).toInt32.toInt =
      max (offsetX p).toInt.natAbs (offsetY p).toInt.natAbs ∧
    (chebyshevDistanceModel p).toBitVec.slt 0#32 = false := by
  have hx32 : (offsetX p).toUInt32 ≠ 0x80000000 := fun h => hx (int32_toUInt32_inj h)
  have hy32 : (offsetY p).toUInt32 ≠ 0x80000000 := fun h => hy (int32_toUInt32_inj h)
  rcases absI32UInt_nonneg_toNat hx32 with ⟨hsx, hnx⟩
  rcases absI32UInt_nonneg_toNat hy32 with ⟨hsy, hny⟩
  dsimp [chebyshevDistanceModel, maxI32UInt]
  have hslt : (absI32UInt (offsetX p).toUInt32).toBitVec.slt (absI32UInt (offsetY p).toUInt32).toBitVec =
      decide (((offsetX p).toInt.natAbs : Int) < ((offsetY p).toInt.natAbs : Int)) := by
    change decide ((absI32UInt (offsetX p).toUInt32).toInt32.toInt <
        (absI32UInt (offsetY p).toUInt32).toInt32.toInt) = _
    rw [absI32UInt_toInt hx32, absI32UInt_toInt hy32]
    rfl
  rw [hslt]
  split
  · next hlt =>
    rw [decide_eq_true_iff] at hlt
    refine ⟨?_, hsy⟩
    rw [absI32UInt_toInt hy32]
    change ((offsetY p).toInt.natAbs : Int) = _
    omega
  · next hge =>
    rw [decide_eq_true_eq] at hge
    refine ⟨?_, hsx⟩
    rw [absI32UInt_toInt hx32]
    change ((offsetX p).toInt.natAbs : Int) = _
    omega

/-- Signed Manhattan distance equals `|x| + |y|` when `|x| + |y| < 2^31`. -/
theorem manhattanDistanceModel_eq_natAdd (p : UInt64)
    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue)
    (hsum : (offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs < 2 ^ 31) :
    (manhattanDistanceModel p).toInt32.toInt =
      ((offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs : Nat) ∧
    (manhattanDistanceModel p).toBitVec.slt 0#32 = false := by
  have hx32 : (offsetX p).toUInt32 ≠ 0x80000000 := fun h => hx (int32_toUInt32_inj h)
  have hy32 : (offsetY p).toUInt32 ≠ 0x80000000 := fun h => hy (int32_toUInt32_inj h)
  rcases absI32UInt_nonneg_toNat hx32 with ⟨_, hnx⟩
  rcases absI32UInt_nonneg_toNat hy32 with ⟨_, hny⟩
  have hnx' : (absI32UInt (offsetX p).toUInt32).toNat = (offsetX p).toInt.natAbs := hnx
  have hny' : (absI32UInt (offsetY p).toUInt32).toNat = (offsetY p).toInt.natAbs := hny
  dsimp [manhattanDistanceModel]
  have hadd : (absI32UInt (offsetX p).toUInt32 + absI32UInt (offsetY p).toUInt32).toNat =
      (offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs := by
    change ((absI32UInt (offsetX p).toUInt32).toNat + (absI32UInt (offsetY p).toUInt32).toNat) % 2 ^ 32 = _
    rw [hnx', hny']
    exact Nat.mod_eq_of_lt (by omega)
  have hti : (absI32UInt (offsetX p).toUInt32 + absI32UInt (offsetY p).toUInt32).toInt32.toInt =
      ((offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs : Nat) := by
    have hcond := uint32_toInt32_toInt (absI32UInt (offsetX p).toUInt32 + absI32UInt (offsetY p).toUInt32)
    rw [hadd] at hcond
    split at hcond <;> omega
  have hslt : (absI32UInt (offsetX p).toUInt32 + absI32UInt (offsetY p).toUInt32).toBitVec.slt 0#32 = false := by
    change decide ((absI32UInt (offsetX p).toUInt32 + absI32UInt (offsetY p).toUInt32).toInt32.toInt < 0) = false
    rw [hti, decide_eq_false_iff_not]
    omega
  exact ⟨hti, hslt⟩

/-- `chebyshevDistanceModel` symmetry under negation `-(x, y)`. -/
theorem chebyshevDistanceModel_neg (x y : Int32) :
    chebyshevDistanceModel (packOffset (-x) (-y)) = chebyshevDistanceModel (packOffset x y) := by
  simp only [chebyshevDistanceModel, offsetX_pack, offsetY_pack, absI32UInt_neg]

/-- `manhattanDistanceModel` symmetry under negation `-(x, y)`. -/
theorem manhattanDistanceModel_neg (x y : Int32) :
    manhattanDistanceModel (packOffset (-x) (-y)) = manhattanDistanceModel (packOffset x y) := by
  simp only [manhattanDistanceModel, offsetX_pack, offsetY_pack, absI32UInt_neg]

/-- `chebyshevDistanceModel` axis symmetry `(x, y) ↔ (y, x)`. -/
theorem chebyshevDistanceModel_swap (x y : Int32) :
    chebyshevDistanceModel (packOffset x y) = chebyshevDistanceModel (packOffset y x) := by
  dsimp [chebyshevDistanceModel, maxI32UInt]
  simp only [offsetX_pack, offsetY_pack]
  by_cases heq : absI32UInt x.toUInt32 = absI32UInt y.toUInt32
  · simp [heq]
  have hlt1 : ∀ a b : UInt32, a ≠ b →
      (if a.toBitVec.slt b.toBitVec then b else a) = if b.toBitVec.slt a.toBitVec then a else b := by
    intro a b hne
    change (if decide (a.toInt32.toInt < b.toInt32.toInt) then b else a) =
      if decide (b.toInt32.toInt < a.toInt32.toInt) then a else b
    have hne_int : a.toInt32.toInt ≠ b.toInt32.toInt := fun h => hne (uint32_toInt32_inj (Int32.toInt.inj h))
    by_cases h1 : a.toInt32.toInt < b.toInt32.toInt
    · simp [h1, show ¬ b.toInt32.toInt < a.toInt32.toInt by omega]
    · simp [h1, show b.toInt32.toInt < a.toInt32.toInt by omega]
  exact hlt1 _ _ heq

/-- `manhattanDistanceModel` axis symmetry `(x, y) ↔ (y, x)`. -/
theorem manhattanDistanceModel_swap (x y : Int32) :
    manhattanDistanceModel (packOffset x y) = manhattanDistanceModel (packOffset y x) := by
  simp only [manhattanDistanceModel, offsetX_pack, offsetY_pack, UInt32.add_comm]

/-- Zero-distance characterization (`L∞(p) = 0 ↔ p = 0`) when coordinates are not `Int32.minValue`. -/
theorem chebyshevDistanceModel_eq_zero_iff (p : UInt64)
    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue) :
    chebyshevDistanceModel p = 0 ↔ p = 0 := by
  rcases chebyshevDistanceModel_eq_natMax p hx hy with ⟨hm, _⟩
  constructor
  · intro h0
    have hzi : (chebyshevDistanceModel p).toInt32.toInt = 0 := by rw [h0]; rfl
    rw [hm] at hzi
    have hx0 : offsetX p = 0 := by
      apply Int32.toInt.inj; change (offsetX p).toInt = 0; omega
    have hy0 : offsetY p = 0 := by
      apply Int32.toInt.inj; change (offsetY p).toInt = 0; omega
    have h := packOffset_unpack p
    rw [hx0, hy0] at h
    exact h.symm
  · intro hp0
    subst hp0
    decide

/-- Norm equivalence `L∞ ≤ L1 ≤ 2 · L∞` on 2D grid offsets within non-overflowing signed `Int32` range. -/
theorem norm_equivalence (p : UInt64)
    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue)
    (hsum : (offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs < 2 ^ 31) :
    (chebyshevDistanceModel p).toInt32.toInt ≤ (manhattanDistanceModel p).toInt32.toInt ∧
    (manhattanDistanceModel p).toInt32.toInt ≤ 2 * (chebyshevDistanceModel p).toInt32.toInt := by
  rcases chebyshevDistanceModel_eq_natMax p hx hy with ⟨hc, _⟩
  rcases manhattanDistanceModel_eq_natAdd p hx hy hsum with ⟨hm, _⟩
  omega

/-- Triangle inequality for `manhattanDistanceModel` in the non-overflowing quarter-range. -/
theorem manhattanDistanceModel_triangle (a b : UInt64)
    (hax : -((2 ^ 28 : Int)) ≤ (offsetX a).toInt ∧ (offsetX a).toInt ≤ 2 ^ 28)
    (hay : -((2 ^ 28 : Int)) ≤ (offsetY a).toInt ∧ (offsetY a).toInt ≤ 2 ^ 28)
    (hbx : -((2 ^ 28 : Int)) ≤ (offsetX b).toInt ∧ (offsetX b).toInt ≤ 2 ^ 28)
    (hby : -((2 ^ 28 : Int)) ≤ (offsetY b).toInt ∧ (offsetY b).toInt ≤ 2 ^ 28) :
    (manhattanDistanceModel (addPackedOffset a b)).toInt32.toInt ≤
      (manhattanDistanceModel a).toInt32.toInt + (manhattanDistanceModel b).toInt32.toInt := by
  have hxa : offsetX a ≠ Int32.minValue := by intro h; rw [h] at hax; revert hax; decide
  have hya : offsetY a ≠ Int32.minValue := by intro h; rw [h] at hay; revert hay; decide
  have hxb : offsetX b ≠ Int32.minValue := by intro h; rw [h] at hbx; revert hbx; decide
  have hyb : offsetY b ≠ Int32.minValue := by intro h; rw [h] at hby; revert hby; decide
  have hma := manhattanDistanceModel_eq_natAdd a hxa hya (by omega)
  have hmb := manhattanDistanceModel_eq_natAdd b hxb hyb (by omega)
  have hx_add : (offsetX (addPackedOffset a b)).toInt = (offsetX a).toInt + (offsetX b).toInt := by
    dsimp [addPackedOffset]; rw [offsetX_pack]
    exact int32_toInt_add_of_bounds (by omega) (by omega)
  have hy_add : (offsetY (addPackedOffset a b)).toInt = (offsetY a).toInt + (offsetY b).toInt := by
    dsimp [addPackedOffset]; rw [offsetY_pack]
    exact int32_toInt_add_of_bounds (by omega) (by omega)
  have hxab_ne : offsetX (addPackedOffset a b) ≠ Int32.minValue := by
    intro h
    have hmin : (Int32.minValue : Int32).toInt = -(2 ^ 31) := by decide
    rw [h, hmin] at hx_add; omega
  have hyab_ne : offsetY (addPackedOffset a b) ≠ Int32.minValue := by
    intro h
    have hmin : (Int32.minValue : Int32).toInt = -(2 ^ 31) := by decide
    rw [h, hmin] at hy_add; omega
  have hmab := manhattanDistanceModel_eq_natAdd (addPackedOffset a b) hxab_ne hyab_ne
    (by rw [hx_add, hy_add]; omega)
  rw [hma.1, hmb.1, hmab.1, hx_add, hy_add]
  omega

/-- Every neighbor produced by `getMooreNeighborsModel o` lies at Chebyshev distance `1` from `o`. -/
theorem getMooreNeighborsModel_chebyshev_one (o : UInt64) :
    ∀ n ∈ getMooreNeighborsModel o, chebyshevDistanceModel (subPackedOffset n o) = 1 := by
  intro n hn
  dsimp [getMooreNeighborsModel, mooreNeighborOffsetsModel, addPackedOffset, subPackedOffset] at hn ⊢
  simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with ⟨⟨dx, dy⟩, hmem, rfl⟩
  simp only [offsetX_pack, offsetY_pack, int32_add_sub_cancel_right]
  rcases hmem with h | h | h | h | h | h | h | h <;> cases h <;> decide

/-- Every neighbor produced by `getVonNeumannNeighborsModel o` lies at Manhattan distance `1` from `o`. -/
theorem getVonNeumannNeighborsModel_manhattan_one (o : UInt64) :
    ∀ n ∈ getVonNeumannNeighborsModel o, manhattanDistanceModel (subPackedOffset n o) = 1 := by
  intro n hn
  dsimp [getVonNeumannNeighborsModel, vonNeumannNeighborOffsetsModel, addPackedOffset, subPackedOffset] at hn ⊢
  simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with ⟨⟨dx, dy⟩, hmem, rfl⟩
  simp only [offsetX_pack, offsetY_pack, int32_add_sub_cancel_right]
  rcases hmem with h | h | h | h <;> cases h <;> decide

/-- Moore neighborhoods contain 8 distinct cells (`Nodup` and `length = 8`). -/
theorem getMooreNeighborsModel_spec (o : UInt64) :
    (getMooreNeighborsModel o).length = 8 ∧ (getMooreNeighborsModel o).Nodup := by
  refine ⟨by rfl, ?_⟩
  dsimp [getMooreNeighborsModel, addPackedOffset]
  have hinj : Function.Injective (fun d : Int32 × Int32 =>
      packOffset (offsetX (packOffset d.1 d.2) + offsetX o)
        (offsetY (packOffset d.1 d.2) + offsetY o)) := by
    intro d1 d2 heq
    have hx := congrArg offsetX heq
    have hy := congrArg offsetY heq
    simp only [offsetX_pack, offsetY_pack] at hx hy
    exact Prod.ext (int32_add_right_cancel hx) (int32_add_right_cancel hy)
  apply List.Nodup.map hinj
  dsimp [mooreNeighborOffsetsModel]
  simp

/-- Von Neumann neighborhoods contain 4 distinct cells (`Nodup` and `length = 4`). -/
theorem getVonNeumannNeighborsModel_spec (o : UInt64) :
    (getVonNeumannNeighborsModel o).length = 4 ∧ (getVonNeumannNeighborsModel o).Nodup := by
  refine ⟨by rfl, ?_⟩
  dsimp [getVonNeumannNeighborsModel, addPackedOffset]
  have hinj : Function.Injective (fun d : Int32 × Int32 =>
      packOffset (offsetX (packOffset d.1 d.2) + offsetX o)
        (offsetY (packOffset d.1 d.2) + offsetY o)) := by
    intro d1 d2 heq
    have hx := congrArg offsetX heq
    have hy := congrArg offsetY heq
    simp only [offsetX_pack, offsetY_pack] at hx hy
    exact Prod.ext (int32_add_right_cancel hx) (int32_add_right_cancel hy)
  apply List.Nodup.map hinj
  dsimp [vonNeumannNeighborOffsetsModel]
  simp

/-- Every Von Neumann neighbor is also a Moore neighbor. -/
theorem getVonNeumannNeighborsModel_subset_moore (o : UInt64) :
    ∀ n ∈ getVonNeumannNeighborsModel o, n ∈ getMooreNeighborsModel o := by
  intro n hn
  dsimp [getVonNeumannNeighborsModel, getMooreNeighborsModel,
    vonNeumannNeighborOffsetsModel, mooreNeighborOffsetsModel] at hn ⊢
  simp only [List.mem_map] at hn ⊢
  rcases hn with ⟨d, hd, rfl⟩
  refine ⟨d, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  rcases hd with rfl | rfl | rfl | rfl <;> decide

/-- `floorModel` unpacks on `x` to the floored `offsetFloatX` coordinate converted to `Int32`. -/
theorem offsetX_floorModel (packed : UInt64) :
    offsetX (floorModel packed) =
      float32ToInt32Model (offsetFloatX packed).toFloat.floor.toFloat32 := by
  dsimp [floorModel]
  exact offsetX_pack _ _

/-- `floorModel` unpacks on `y` to the floored `offsetFloatY` coordinate converted to `Int32`. -/
theorem offsetY_floorModel (packed : UInt64) :
    offsetY (floorModel packed) =
      float32ToInt32Model (offsetFloatY packed).toFloat.floor.toFloat32 := by
  dsimp [floorModel]
  exact offsetY_pack _ _

/-- `signumFloat32` always returns `NaN`, a zero (`±0.0`), `-1.0`, or `1.0`. -/
theorem signumFloat32_range (x : Float32) :
    (signumFloat32 x).isNaN = true ∨
    (signumFloat32 x == 0.0) = true ∨
    signumFloat32 x = (-1.0 : Float32) ∨
    signumFloat32 x = (1.0 : Float32) := by
  dsimp [signumFloat32]
  by_cases h0 : (x.isNaN || x == 0.0) = true
  · simp only [h0, ↓reduceIte]
    rcases Bool.or_eq_true_iff.mp h0 with hnan | hzero
    · exact Or.inl hnan
    · exact Or.inr (Or.inl hzero)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases hneg : x < 0.0
    · simp [hneg]
    · simp [hneg]

/-- `sideOfLineModel` always returns `NaN`, a zero (`±0.0`), `-1.0`, or `1.0`. -/
theorem sideOfLineModel_range (point startPt endPt : UInt64) :
    (sideOfLineModel point startPt endPt).isNaN = true ∨
    (sideOfLineModel point startPt endPt == 0.0) = true ∨
    sideOfLineModel point startPt endPt = (-1.0 : Float32) ∨
    sideOfLineModel point startPt endPt = (1.0 : Float32) :=
  signumFloat32_range _

end Geometry.KotlinModel

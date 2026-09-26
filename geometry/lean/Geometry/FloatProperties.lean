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

import Geometry.Basic
import Geometry.Bridge
import Geometry.FloatModel
import Geometry.FloatSemantics
import Geometry.FloatBounds
import Geometry.LineSegment
import Geometry.Properties
import Mathlib.Data.Rat.Cast.Order

namespace Geometry

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange


/--
A Point32 has finite coordinates if both x and y are neither NaN nor infinite.
-/
def Point32.isFinite (p : Point32) : Prop :=
  binary32IsFinite p.x = true ∧ binary32IsFinite p.y = true

theorem toRat?_isSome_of_isFinite (x : Binary32) (hx : binary32IsFinite x = true) :
    ∃ q : ℚ, ExecFloat.Binary.toRat? x = some q := by
  have h_model_fin : ExecFloat.Binary.isFinite x = true := hx
  unfold binary32IsFinite ExecFloat.Binary.isFinite at hx
  unfold ExecFloat.Binary.toRat?
  have h_ieee_fin : Formats.BinaryInterchange.Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  unfold Model.toRat?
  rw [h_dyadic]
  exact ⟨d.toRat, rfl⟩

theorem floorBinary32_eq_toInt_binary32ToRat (f : Binary32) (h_fin : binary32IsFinite f = true) :
    floorBinary32 f = toInt (binary32ToRat f) := by
  obtain ⟨q, hq⟩ := toRat?_isSome_of_isFinite f h_fin
  unfold floorBinary32 binary32ToRat toInt
  rw [hq]
  simp

theorem floorPoint32_eq_floorPoint (p : Point32) (h_fin : p.isFinite) :
    floorPoint32 p = floorPoint p.toPoint := by
  unfold floorPoint32 floorPoint Point32.toPoint
  rcases h_fin with ⟨hx, hy⟩
  rw [floorBinary32_eq_toInt_binary32ToRat p.x hx]
  rw [floorBinary32_eq_toInt_binary32ToRat p.y hy]

theorem toReal_eq_cast_toRat (x : Binary32) (hx : binary32IsFinite x = true) :
    Model.toReal (ExecFloat.Binary.toModel x) = ((binary32ToRat x : ℚ) : ℝ) := by
  have h_model_fin : ExecFloat.Binary.isFinite x = true := hx
  unfold binary32IsFinite ExecFloat.Binary.isFinite at hx
  have h_ieee_fin : Model.IEEE.isFinite (ExecFloat.Binary.toModel x) = true := hx
  obtain ⟨d, hd⟩ := Model.exists_ieeeToDyadic?_of_isFinite h_ieee_fin
  have h_dyadic : Model.toDyadic? (ExecFloat.Binary.toModel x) = some d := by
    unfold Model.toDyadic?
    simp [hd]
  have h_toRat : ExecFloat.Binary.toRat? x = some d.toRat := by
    unfold ExecFloat.Binary.toRat? Model.toRat?
    rw [h_dyadic]
    rfl
  have h_rat : binary32ToRat x = d.toRat := by
    unfold binary32ToRat
    rw [h_toRat]
    rfl
  rw [h_rat]
  unfold Model.toReal Model.toReal?
  rw [h_dyadic]
  exact (Dyadic.cast_toRat d).symm

theorem compareLess_iff_toRat_lt (x y : Binary32)
    (hx : binary32IsFinite x = true) (hy : binary32IsFinite y = true) :
    (x < y) ↔ binary32ToRat x < binary32ToRat y := by
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  have hx_fin : Model.isFinite (ExecFloat.Binary.toModel x) = true := hx
  have hy_fin : Model.isFinite (ExecFloat.Binary.toModel y) = true := hy
  rw [Model.compare_eq_some_lt_iff_toReal_lt_of_isFinite
    (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx_fin hy_fin]
  rw [toReal_eq_cast_toRat x hx]
  rw [toReal_eq_cast_toRat y hy]
  exact Rat.cast_lt

theorem compareGreater_iff_toRat_gt (x y : Binary32)
    (hx : binary32IsFinite x = true) (hy : binary32IsFinite y = true) :
    (x > y) ↔ binary32ToRat x > binary32ToRat y :=
  compareLess_iff_toRat_lt y x hy hx






/--
Discrete Hausdorff distance bound: every cell in `cells1` is within Chebyshev distance `d`
of some cell in `cells2`, and vice-versa.
-/
def cellHausdorffDistanceLe (cells1 cells2 : List Cell) (d : Nat) : Prop :=
  (∀ c1 ∈ cells1, ∃ c2 ∈ cells2, chebyshevDistance c1 c2 ≤ d) ∧
  (∀ c2 ∈ cells2, ∃ c1 ∈ cells1, chebyshevDistance c1 c2 ≤ d)

/--
Identical cell collections trivially have Hausdorff distance 0 (and therefore ≤ 1).
-/
theorem cellHausdorffDistanceLe_refl (cells : List Cell) :
    cellHausdorffDistanceLe cells cells 0 := by
  constructor
  · intro c hc
    refine ⟨c, hc, ?_⟩
    unfold chebyshevDistance
    simp
  · intro c hc
    refine ⟨c, hc, ?_⟩
    unfold chebyshevDistance
    simp

theorem cellHausdorffDistanceLe_of_eq {cells1 cells2 : List Cell} (h : cells1 = cells2) :
    cellHausdorffDistanceLe cells1 cells2 1 := by
  subst h
  have h0 := cellHausdorffDistanceLe_refl cells1
  rcases h0 with ⟨h1, h2⟩
  constructor
  · intro c hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩
  · intro c hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩

/--
Reduces the Hausdorff distance bound between deduplicated cell lists with matching endpoints
to proving that intermediate cells are within Chebyshev distance at most 1.
-/
theorem cellHausdorffDistanceLe_dedup_endpoints (s e : Cell) (rest1 rest2 : List Cell)
    (h1 : ∀ c1 ∈ rest1, ∃ c2 ∈ dedupCells ([s, e] ++ rest2), chebyshevDistance c1 c2 ≤ 1)
    (h2 : ∀ c2 ∈ rest2, ∃ c1 ∈ dedupCells ([s, e] ++ rest1), chebyshevDistance c1 c2 ≤ 1) :
    cellHausdorffDistanceLe (dedupCells ([s, e] ++ rest1)) (dedupCells ([s, e] ++ rest2)) 1 := by
  constructor
  · intro c1 hc1
    rw [mem_dedupCells] at hc1
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc1
    rcases hc1 with (rfl | rfl) | hrest1
    · refine ⟨c1, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · refine ⟨c1, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · exact h1 c1 hrest1
  · intro c2 hc2
    rw [mem_dedupCells] at hc2
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc2
    rcases hc2 with (rfl | rfl) | hrest2
    · refine ⟨c2, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · refine ⟨c2, ?_, ?_⟩
      · rw [mem_dedupCells]
        simp
      · rw [chebyshevDistance_self]; omega
    · exact h2 c2 hrest2

/--
When single-step transitions agree between floating-point and rational stepping,
the entire multi-step raymarching sequence produces identical cell lists by induction on fuel.
-/
theorem rayMarchFloat_eq_rayMarch (fuel : Nat) (start : Point32) (ptEnd : Point32)
    (dx dy : Binary32) (stepX stepY : Int) (endCell : Cell) (current : Cell) (acc : List Cell)
    (h_step : ∀ c, rayMarchStepFloat start dx dy stepX stepY c =
      rayMarchStep ⟨binary32ToRat start.x, binary32ToRat start.y⟩ ⟨binary32ToRat ptEnd.x, binary32ToRat ptEnd.y⟩
        (binary32ToRat ptEnd.x - binary32ToRat start.x) (binary32ToRat ptEnd.y - binary32ToRat start.y)
        stepX stepY c) :
    rayMarchFloat fuel start dx dy stepX stepY endCell current acc =
    rayMarch fuel ⟨binary32ToRat start.x, binary32ToRat start.y⟩ ⟨binary32ToRat ptEnd.x, binary32ToRat ptEnd.y⟩
      (binary32ToRat ptEnd.x - binary32ToRat start.x) (binary32ToRat ptEnd.y - binary32ToRat start.y)
      stepX stepY endCell current acc := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ fuel ih =>
    unfold rayMarchFloat rayMarch
    by_cases h_end : current == endCell
    · simp [h_end]
    · simp only [h_end, Bool.false_eq_true, ↓reduceIte]
      rw [h_step current]
      cases (rayMarchStep ⟨binary32ToRat start.x, binary32ToRat start.y⟩
        ⟨binary32ToRat ptEnd.x, binary32ToRat ptEnd.y⟩
        (binary32ToRat ptEnd.x - binary32ToRat start.x)
        (binary32ToRat ptEnd.y - binary32ToRat start.y) stepX stepY current) with
      | mk nextCell done =>
        dsimp only []
        by_cases h_done : done = true
        · simp [h_done]
        · simp only [h_done, Bool.false_eq_true, ↓reduceIte]
          exact ih nextCell (acc ++ [nextCell])

/--
When endpoint floors and step transitions agree between the 32-bit floating point model
and the exact rational specification, their output cell intersection lists are strictly identical.
-/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_step_eq
    (A B : Point32)
    (h_floorA : floorPoint32 A = floorPoint ⟨binary32ToRat A.x, binary32ToRat A.y⟩)
    (h_floorB : floorPoint32 B = floorPoint ⟨binary32ToRat B.x, binary32ToRat B.y⟩)
    (h_stepX : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
      (if binary32ToRat B.x - binary32ToRat A.x > 0 then 1
       else if binary32ToRat B.x - binary32ToRat A.x < 0 then -1 else 0))
    (h_stepY : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
      (if binary32ToRat B.y - binary32ToRat A.y > 0 then 1
       else if binary32ToRat B.y - binary32ToRat A.y < 0 then -1 else 0))
    (h_step : ∀ c,
      rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c =
      rayMarchStep ⟨binary32ToRat A.x, binary32ToRat A.y⟩ ⟨binary32ToRat B.x, binary32ToRat B.y⟩
        (binary32ToRat B.x - binary32ToRat A.x) (binary32ToRat B.y - binary32ToRat A.y)
        (if binary32ToRat B.x - binary32ToRat A.x > 0 then 1
         else if binary32ToRat B.x - binary32ToRat A.x < 0 then -1 else 0)
        (if binary32ToRat B.y - binary32ToRat A.y > 0 then 1
         else if binary32ToRat B.y - binary32ToRat A.y < 0 then -1 else 0) c) :
    cellIntersectionsSegmentFloat A B =
    cellIntersectionsSegment ⟨binary32ToRat A.x, binary32ToRat A.y⟩ ⟨binary32ToRat B.x, binary32ToRat B.y⟩ := by
  unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
  dsimp only []
  rw [h_floorA, h_floorB]
  by_cases h_same : floorPoint ⟨binary32ToRat A.x, binary32ToRat A.y⟩ ==
      floorPoint ⟨binary32ToRat B.x, binary32ToRat B.y⟩
  · simp [h_same]
  · simp only [h_same, Bool.false_eq_true, ↓reduceIte]
    have h_call := rayMarchFloat_eq_rayMarch
      (((floorPoint ⟨binary32ToRat B.x, binary32ToRat B.y⟩).x -
        (floorPoint ⟨binary32ToRat A.x, binary32ToRat A.y⟩).x).natAbs +
       ((floorPoint ⟨binary32ToRat B.x, binary32ToRat B.y⟩).y -
        (floorPoint ⟨binary32ToRat A.x, binary32ToRat A.y⟩).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
      (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
      (floorPoint ⟨binary32ToRat B.x, binary32ToRat B.y⟩)
      (floorPoint ⟨binary32ToRat A.x, binary32ToRat A.y⟩)
      []
      (by
        intro c
        have hc := h_step c
        rw [← h_stepX, ← h_stepY] at hc
        exact hc)
    rw [h_call]
    rw [h_stepX, h_stepY]


/--
Master Theorem 1 (Non-Grazing Equivalence):
When the continuous line segment maintains sufficient clearance from integer grid corners,
has coordinates bounded by `M`, and finite inputs, the floating-point raymarching algorithm
produces the exact same set of discrete intersected cells as the idealized rational algorithm.
-/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_clearance
    (A B : Point32) (M : ℚ)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (_h_bound : inCoordBounds M A.toPoint B.toPoint)
    (h_clear : HasCornerClearance A.toPoint B.toPoint M) :
    cellIntersectionsSegmentFloat A B = cellIntersectionsSegment A.toPoint B.toPoint := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
  have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
  rcases h_clear with ⟨_, h_steps⟩
  rcases h_steps A B rfl rfl with ⟨h_stepX, h_stepY, h_step⟩
  exact cellIntersectionsSegmentFloat_eq_ideal_of_step_eq A B h_floorA h_floorB h_stepX h_stepY h_step

/--
Master Theorem 2 (Cell Hausdorff Bound):
For any input segment with coordinates bounded by `M`, finite inputs, and corner clearance,
the discrete Chebyshev Hausdorff distance between the floating point output
`cellIntersectionsSegmentFloat A B` and the idealized rational output
`cellIntersectionsSegment A.toPoint B.toPoint` is at most 1.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound
    (A B : Point32) (M : ℚ)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds M A.toPoint B.toPoint)
    (h_clear : HasCornerClearance A.toPoint B.toPoint M) :
    cellHausdorffDistanceLe (cellIntersectionsSegmentFloat A B) (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_eq := cellIntersectionsSegmentFloat_eq_ideal_of_clearance A B M h_finiteA h_finiteB h_bound h_clear
  exact cellHausdorffDistanceLe_of_eq h_eq

/--
Unconditional Hausdorff bound for segments within the same discrete grid cell.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_same_cell
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe (cellIntersectionsSegmentFloat A B) (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
  have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
  have h_same_ideal : floorPoint A.toPoint = floorPoint B.toPoint := by
    rw [← h_floorA, ← h_floorB, h_same]
  unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
  rw [h_same, h_same_ideal]
  simp
  rw [h_floorB]
  exact cellHausdorffDistanceLe_of_eq rfl

/--
Unconditional Hausdorff bound when floating-point and idealized single-step raymarching transitions agree.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_of_step_eq
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_stepX : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
      (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0))
    (h_stepY : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
      (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0))
    (h_step : ∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1 =
      (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1)
    (h_done : ∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2 =
      (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
        (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
        (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  by_cases h_same : floorPoint32 A = floorPoint32 B
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_same_cell A B h_finiteA h_finiteB h_same
  · have h_floorA := floorPoint32_eq_floorPoint A h_finiteA
    have h_floorB := floorPoint32_eq_floorPoint B h_finiteB
    have h_same_ideal : floorPoint A.toPoint ≠ floorPoint B.toPoint := by
      rw [← h_floorA, ← h_floorB]; exact h_same
    have h_same_bool : (floorPoint32 A == floorPoint32 B) = false := by
      cases h : (floorPoint32 A == floorPoint32 B)
      · rfl
      · exfalso; apply h_same; rw [eq_of_beq h]
    have h_same_ideal_bool : (floorPoint A.toPoint == floorPoint B.toPoint) = false := by
      cases h : (floorPoint A.toPoint == floorPoint B.toPoint)
      · rfl
      · exfalso; apply h_same_ideal; rw [eq_of_beq h]
    unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
    dsimp only []
    rw [h_same_bool, h_same_ideal_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h_floorA, h_floorB]
    have hX : (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = -1 ∨
              (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = 0 ∨
              (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) = 1 := by
      split_ifs <;> simp
    have hY : (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = -1 ∨
              (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = 0 ∨
              (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) = 1 := by
      split_ifs <;> simp
    have h1 := rayMarchFloat_near_rayMarch_endpoints
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
      (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      hX hY
      (by intro c; exact h_step c)
      (by intro c; exact h_done c)
    have h2 := rayMarch_near_rayMarchFloat_endpoints
      (((floorPoint B.toPoint).x - (floorPoint A.toPoint).x).natAbs +
       ((floorPoint B.toPoint).y - (floorPoint A.toPoint).y).natAbs + 2)
      A B.toPoint (B.x - A.x) (B.y - A.y)
      (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
      (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
      (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0)
      (floorPoint B.toPoint) (floorPoint A.toPoint)
      hX hY
      (by intro c; exact h_step c)
      (by intro c; exact h_done c)
    rw [← h_stepX, ← h_stepY]
    apply cellHausdorffDistanceLe_dedup_endpoints
    · exact h1
    · exact h2

/--
Master Theorem: Discrete Hausdorff bound when segments share a cell, maintain corner clearance,
or exhibit step agreement between floating point and rational raymarching.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_of_clearance_or_step_eq
    (A B : Point32) (M : ℚ)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds M A.toPoint B.toPoint)
    (h : floorPoint32 A = floorPoint32 B ∨
         HasCornerClearance A.toPoint B.toPoint M ∨
         ( (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
             (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0) ∧
           (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
             (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2) )) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  rcases h with h_same | h_clear | ⟨h_stepX, h_stepY, h_step, h_done⟩
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_same_cell A B h_finiteA h_finiteB h_same
  · exact cellIntersectionsSegmentFloat_hausdorff_bound A B M h_finiteA h_finiteB h_bound h_clear
  · exact cellIntersectionsSegmentFloat_hausdorff_bound_of_step_eq
      A B h_finiteA h_finiteB h_stepX h_stepY h_step h_done

/--
Discrete cell Hausdorff distance bound for segments with coordinates bounded by M ≤ 1447,
when either clearance, step agreement, or common endpoint cells hold.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_1447_of_conditions
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds 1447 A.toPoint B.toPoint)
    (h : floorPoint32 A = floorPoint32 B ∨
         HasCornerClearance A.toPoint B.toPoint 1447 ∨
         ( (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
             (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0) ∧
           (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
             (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2) )) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_of_clearance_or_step_eq A B 1447 h_finiteA h_finiteB h_bound h

/--
Discrete cell Hausdorff distance bound for segments with coordinates bounded by M ≤ 1000,
when either clearance, step agreement, or common endpoint cells hold.
-/
theorem cellIntersectionsSegmentFloat_hausdorff_bound_1000_of_conditions
    (A B : Point32)
    (h_finiteA : A.isFinite)
    (h_finiteB : B.isFinite)
    (h_bound : inCoordBounds 1000 A.toPoint B.toPoint)
    (h : floorPoint32 A = floorPoint32 B ∨
         HasCornerClearance A.toPoint B.toPoint 1000 ∨
         ( (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0) =
             (if B.toPoint.x - A.toPoint.x > 0 then 1 else if B.toPoint.x - A.toPoint.x < 0 then -1 else 0) ∧
           (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) =
             (if B.toPoint.y - A.toPoint.y > 0 then 1 else if B.toPoint.y - A.toPoint.y < 0 then -1 else 0) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).1) ∧
           (∀ c, (rayMarchStepFloat A (B.x - A.x) (B.y - A.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2 =
             (rayMarchStep A.toPoint B.toPoint (B.toPoint.x - A.toPoint.x) (B.toPoint.y - A.toPoint.y)
               (if B.x - A.x > 0.0 then 1 else if B.x - A.x < 0.0 then -1 else 0)
               (if B.y - A.y > 0.0 then 1 else if B.y - A.y < 0.0 then -1 else 0) c).2) )) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 :=
  cellIntersectionsSegmentFloat_hausdorff_bound_of_clearance_or_step_eq A B 1000 h_finiteA h_finiteB h_bound h

/--
Alias for Master Theorem 1 matching verification plan naming.
-/
abbrev cellIntersections_float_eq_ideal_of_clearance :=
  @cellIntersectionsSegmentFloat_eq_ideal_of_clearance

/--
Alias for Master Theorem 2 matching verification plan naming.
-/
abbrev cellIntersections_float_hausdorff_bound :=
  @cellIntersectionsSegmentFloat_hausdorff_bound

end Geometry



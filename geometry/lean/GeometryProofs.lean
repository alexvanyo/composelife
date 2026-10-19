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

import models.Basic
import Geometry.LineSegment
import models.FloatModel
import GeometryDefs
import proofs.Interval
import proofs.RayMarchStep
import proofs.Soundness
import proofs.Completeness
import proofs.FloatSemantics
import proofs.FloatBounds
import proofs.FloatAnalysis
import proofs.FloatProperties
import proofs.Continuous
import proofs.Hausdorff
import proofs.CompiledRayMarch
import proofs.Connectivity

namespace Geometry


theorem cellIntersectionsSegment_exact_iff_Impl (A B : Point) (c : Cell) :
    c ∈ cellIntersectionsSegment A B ↔ ActiveIntersectedCell c A B := by
  apply cellIntersectionsSegment_exact_iff_reduction
  intro hne hcA hcB
  have h_sound : ∀ x, x ∈ rayMarch (((floorPoint B).x - (floorPoint A).x).natAbs + ((floorPoint B).y - (floorPoint A).y).natAbs + 2)
      A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0)
      (floorPoint B) (floorPoint A) [] →
      inBoundingBox x A B = true ∧
      ∃ tEnter tExit, cellIntersectionInterval x A B = some (tEnter, tExit) ∧ tEnter < tExit := by
    intro x hx
    exact rayMarch_soundness A B x hx
  apply rayMarch_iff_intermediate_of_mem_eq A B c hcA hcB
  · intro x hxA hxB
    apply rayMarchIntermediateCells_iff_intermediateCells A B x hxA hxB
    · exact h_sound x
    · intro h_bbox h_int
      exact rayMarch_completeness A B x hxA hxB h_bbox h_int
  · intro hray
    rcases h_sound c hray with ⟨h_bbox, tEnter, tExit, h_int, h_lt⟩
    exact not_off_axis_of_interval_lt c A B hcA hcB h_bbox tEnter tExit h_int h_lt

/--
Completeness against continuous geometry: every cell whose open interior the segment passes
through is in the output.
-/
theorem cellIntersectionsSegment_complete_Impl (A B : Point) (c : Cell)
    (h : CellCrossedBySegment c A B) : c ∈ cellIntersectionsSegment A B := by
  obtain ⟨p, hseg, hint⟩ := h
  have hfloor := floorPoint_of_interior hint
  by_cases hcA : c = floorPoint A
  · rw [hcA]
    exact (endpoints_in_cellIntersectionsSegment A B).1
  by_cases hcB : c = floorPoint B
  · rw [hcB]
    exact (endpoints_in_cellIntersectionsSegment A B).2
  rcases hseg with hpA | hpB | ⟨t, ht0, ht1, hx, hy⟩
  · exact absurd (hpA ▸ hfloor).symm hcA
  · exact absurd (hpB ▸ hfloor).symm hcB
  have hp : p = ⟨A.x + t * (B.x - A.x), A.y + t * (B.y - A.y)⟩ := by
    cases p
    simp only at hx hy
    rw [hx, hy]
  subst hp
  have ht0' : 0 < t := by
    refine lt_of_le_of_ne ht0 ?_
    rintro rfl
    apply hcA
    rw [← hfloor]
    congr 1
    simp
  have ht1' : t < 1 := by
    refine lt_of_le_of_ne ht1 ?_
    rintro rfl
    apply hcB
    rw [← hfloor]
    congr 1
    simp
  obtain ⟨tEnter, tExit, h_int, h_lt⟩ := interval_lt_of_interior c A B t ht0' ht1' hint
  have hbbox : inBoundingBox c A B = true := by
    have hx' : Rat.floor (A.x + t * (B.x - A.x)) = c.x := congrArg Cell.x hfloor
    have hy' : Rat.floor (A.y + t * (B.y - A.y)) = c.y := congrArg Cell.y hfloor
    have bx := floor_between A.x B.x t ht0 ht1
    have byy := floor_between A.y B.y t ht0 ht1
    unfold inBoundingBox
    rw [hx'] at bx
    rw [hy'] at byy
    simp only [floorPoint, toInt, Bool.and_eq_true]
    refine ⟨⟨⟨decide_eq_true ?_, decide_eq_true ?_⟩, decide_eq_true ?_⟩, decide_eq_true ?_⟩ <;> omega
  obtain ⟨hsi, hoff⟩ := cell_active_of_interval_lt c A B hcA hcB hbbox tEnter tExit h_int h_lt
  rw [cellIntersectionsSegment_exact_iff_Impl]
  refine ⟨Or.inr (Or.inr ⟨(inBoundingBox_iff_mem_candidateCells A B c).mp hbbox, hsi⟩), ?_⟩
  rintro ⟨_, _, hoff'⟩
  rw [hoff] at hoff'
  contradiction

theorem cellIntersectionsSegmentFloat_contains_endpoints_Impl (A B : Point32) :
    floorPoint32 A ∈ cellIntersectionsSegmentFloat A B ∧
    floorPoint32 B ∈ cellIntersectionsSegmentFloat A B :=
  ⟨cellIntersectionsSegmentFloat_contains_start A B,
   cellIntersectionsSegmentFloat_contains_end A B⟩

theorem rayMarchSegmentCoords_same_cell_Impl (x y : Float) (cx cy : Int32) :
    rayMarchSegmentCoords x y x y cx cy cx cy = #[(cx, cy)] := by
  unfold rayMarchSegmentCoords
  simp

theorem inCoordBounds_main_of_compiled {A B : Point} (h : inCoordBounds compiledCoordBound A B) :
    inCoordBounds mainCoordBound A B := by
  have hle : compiledCoordBound ≤ mainCoordBound := by
    unfold compiledCoordBound mainCoordBound mainCoordBoundNat; norm_num
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨le_trans h1 hle, le_trans h2 hle, le_trans h3 hle, le_trans h4 hle⟩

theorem rayMarchSegmentCoords_hausdorff_bound_Impl (A B : Point32) (sx sy ex ey : Float)
    (cx cy ex' ey' : Int32) (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    cellHausdorffDistanceLe
      (dedupCells (toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey')))
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  rw [rayMarchSegmentCoords_refines_Impl A B sx sy ex ey cx cy ex' ey' hPre]
  exact cellIntersectionsSegmentFloat_hausdorff_bound_Impl A B hPre.h_finite.1 hPre.h_finite.2
    (inCoordBounds_main_of_compiled hPre.h_bound)

theorem rayMarchSegmentCoords_connected_Impl (A B : Point32) (sx sy ex ey : Float)
    (cx cy ex' ey' : Int32) (hPre : InRange A B sx sy ex ey cx cy ex' ey') :
    ∃ path : List Cell, path.head? = some (floorPoint32 A) ∧ path.getLast? = some (floorPoint32 B) ∧
      CellPathConnected path ∧
      ∀ c, c ∈ path ↔ c ∈ toCells (rayMarchSegmentCoords sx sy ex ey cx cy ex' ey') := by
  obtain ⟨path, hh, hl, hc, hm⟩ := cellIntersectionsSegmentFloat_connected_Impl A B hPre.h_finite.1
    hPre.h_finite.2 (inCoordBounds_main_of_compiled hPre.h_bound)
  refine ⟨path, hh, hl, hc, fun c => ?_⟩
  rw [hm, ← rayMarchSegmentCoords_refines_Impl A B sx sy ex ey cx cy ex' ey' hPre, mem_dedupCells]

end Geometry

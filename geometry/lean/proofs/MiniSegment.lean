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
import models.FloatModel
import GeometryDefs
import proofs.FloatSemantics
import proofs.FloatBounds
import proofs.FloatProperties
import proofs.FloatAnalysis
import proofs.Interval
import proofs.Soundness
import proofs.RayMarchLimits
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances

namespace Geometry

/--
When two floating-point points reside in the same discrete grid cell,
the floating-point and idealized rational segment intersection lists are strictly identical.
-/
theorem cellIntersectionsSegmentFloat_eq_ideal_of_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellIntersectionsSegmentFloat A B = cellIntersectionsSegment A.toPoint B.toPoint := by
  have h_floorA := floorPoint32_eq_floorPoint A h_finA
  have h_floorB := floorPoint32_eq_floorPoint B h_finB
  unfold cellIntersectionsSegmentFloat cellIntersectionsSegment
  dsimp only []
  have h_same_bool : (floorPoint32 A == floorPoint32 B) = true := by
    rw [h_same, beq_self_eq_true]
  have h_ideal : floorPoint A.toPoint = floorPoint B.toPoint := by
    rw [← h_floorA, ← h_floorB, h_same]
  have h_ideal_bool : (floorPoint A.toPoint == floorPoint B.toPoint) = true := by
    rw [h_ideal, beq_self_eq_true]
  rw [h_same_bool, h_ideal_bool]
  simp only [ite_true]
  rw [h_floorA]

/--
When two floating-point points reside in the same discrete grid cell,
the discrete Chebyshev Hausdorff distance between float and rational outputs is 0.
-/
theorem cellIntersectionsSegmentFloat_sub_hausdorff_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 0 := by
  have h_eq := cellIntersectionsSegmentFloat_eq_ideal_of_same_cell A B h_finA h_finB h_same
  rw [h_eq]
  exact cellHausdorffDistanceLe_refl _

/--
When two points reside in the same cell, the Hausdorff distance is also at most 1.
-/
theorem cellIntersectionsSegmentFloat_sub_hausdorff_one_of_same_cell
    (A B : Point32) (h_finA : A.isFinite) (h_finB : B.isFinite)
    (h_same : floorPoint32 A = floorPoint32 B) :
    cellHausdorffDistanceLe
      (cellIntersectionsSegmentFloat A B)
      (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  have h0 := cellIntersectionsSegmentFloat_sub_hausdorff_same_cell A B h_finA h_finB h_same
  rcases h0 with ⟨h1, h2⟩
  constructor
  · intro c hc
    rcases h1 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩
  · intro c hc
    rcases h2 c hc with ⟨c', hc', hd⟩
    exact ⟨c', hc', by omega⟩

theorem cellIntersectionsSegmentFloat_contains_start (A B : Point32) :
    floorPoint32 A ∈ cellIntersectionsSegmentFloat A B := by
  unfold cellIntersectionsSegmentFloat; dsimp only []
  cases h : (floorPoint32 A == floorPoint32 B)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mem_dedupCells]
    simp only [List.mem_append, List.mem_cons, true_or]
  · simp only [ite_true, List.mem_singleton]


end Geometry


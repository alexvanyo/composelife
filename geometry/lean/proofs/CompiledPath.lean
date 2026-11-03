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

import GeometryDefs
import proofs.Interval
import proofs.MiniSegment
import proofs.CompiledRayMarch
import proofs.Hausdorff

/-!
# Compiled polylines

`cellIntersections(points)` in `LineSegment.kt` calls the compiled ray march once per segment and collects the
cells into a set. This file proves that the cells collected this way are exactly the cells of the float polyline
model `cellIntersectionsPathFloat`, and transfers the polyline Hausdorff bound to them.
-/

namespace Geometry

theorem mem_compiledPathCells_cons (k : SegmentCall) (ks : List SegmentCall) (c : Cell) :
    c ∈ compiledPathCells (k :: ks) ↔
      c ∈ toCells (rayMarchSegmentCoords k.sx k.sy k.ex k.ey k.cx k.cy k.ex' k.ey') ∨ c ∈ compiledPathCells ks := by
  simp [compiledPathCells]

theorem compiledPathCells_mem_iff_Impl :
    ∀ (Ps : List Point32) (calls : List SegmentCall), 2 ≤ Ps.length → PathInRange Ps calls →
      ∀ c, c ∈ compiledPathCells calls ↔ c ∈ cellIntersectionsPathFloat Ps
  | [], _, h, _, _ => by simp at h
  | [_], _, h, _, _ => by simp at h
  | p1 :: p2 :: rest, [], _, h, _ => by simp [PathInRange] at h
  | p1 :: p2 :: rest, k :: ks, _, h, c => by
    obtain ⟨hk, hks⟩ := h
    have hseg : ∀ c, c ∈ toCells (rayMarchSegmentCoords k.sx k.sy k.ex k.ey k.cx k.cy k.ex' k.ey') ↔
        c ∈ cellIntersectionsSegmentFloat p1 p2 := by
      intro c
      rw [← rayMarchSegmentCoords_refines_Impl p1 p2 _ _ _ _ _ _ _ _ hk, mem_dedupCells]
    rw [mem_compiledPathCells_cons, hseg]
    simp only [cellIntersectionsPathFloat, mem_dedupCells, List.mem_append]
    cases rest with
    | nil =>
      cases ks with
      | nil =>
        simp only [compiledPathCells, List.flatMap_nil, List.not_mem_nil, or_false, cellIntersectionsPathFloat,
          List.mem_singleton]
        constructor
        · exact Or.inl
        · rintro (h | rfl)
          · exact h
          · exact cellIntersectionsSegmentFloat_contains_end p1 p2
      | cons _ _ => simp [PathInRange] at hks
    | cons p3 rest =>
      rw [compiledPathCells_mem_iff_Impl (p2 :: p3 :: rest) ks (by simp) hks c]

theorem cellHausdorffDistanceLe_congr_left {l l' r : List Cell} {d : Nat} (h : ∀ c, c ∈ l ↔ c ∈ l')
    (hd : cellHausdorffDistanceLe l' r d) : cellHausdorffDistanceLe l r d := by
  obtain ⟨h1, h2⟩ := hd
  refine ⟨fun c hc => h1 c ((h c).mp hc), fun c hc => ?_⟩
  obtain ⟨c1, hc1, hd1⟩ := h2 c hc
  exact ⟨c1, (h c1).mpr hc1, hd1⟩

theorem PathInRange.get : ∀ {Ps : List Point32} {calls : List SegmentCall}, PathInRange Ps calls →
    ∀ (i : Nat) (hi : i + 1 < Ps.length), ∃ k : SegmentCall,
      InRange (Ps.get ⟨i, by omega⟩) (Ps.get ⟨i + 1, hi⟩) k.sx k.sy k.ex k.ey k.cx k.cy k.ex' k.ey'
  | [], _, h, _, hi => by simp at hi
  | [_], _, _, _, hi => by simp at hi
  | _ :: _ :: _, [], h, _, _ => by simp [PathInRange] at h
  | p1 :: p2 :: rest, k :: ks, h, i, hi => by
    obtain ⟨hk, hks⟩ := h
    cases i with
    | zero => exact ⟨k, hk⟩
    | succ i =>
      obtain ⟨k', hk'⟩ := PathInRange.get hks i (by simpa using hi)
      exact ⟨k', by simpa using hk'⟩

theorem PathInRange.allFinite : ∀ {Ps : List Point32} {calls : List SegmentCall}, PathInRange Ps calls →
    2 ≤ Ps.length → AllFinite Ps := by
  intro Ps calls h hlen p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  by_cases hlast : i + 1 < Ps.length
  · obtain ⟨k, hk⟩ := h.get i hlast
    simpa using hk.h_finite.1
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨k, hk⟩ := h.get j (by omega)
    simpa using hk.h_finite.2

theorem inCoordBounds_main_of_compiled {A B : Point} (h : inCoordBounds compiledCoordBound A B) :
    inCoordBounds mainCoordBound A B := by
  have hle : compiledCoordBound ≤ mainCoordBound := by
    unfold compiledCoordBound mainCoordBound mainCoordBoundNat; norm_num
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨le_trans h1 hle, le_trans h2 hle, le_trans h3 hle, le_trans h4 hle⟩

theorem compiledPathCells_hausdorff_bound_Impl (Ps : List Point32) (calls : List SegmentCall)
    (hlen : 2 ≤ Ps.length) (h : PathInRange Ps calls) :
    cellHausdorffDistanceLe (compiledPathCells calls) (cellIntersectionsPath (pointsToRational Ps)) 1 := by
  apply cellHausdorffDistanceLe_congr_left (compiledPathCells_mem_iff_Impl Ps calls hlen h)
  apply cellIntersectionsPathFloat_hausdorff_bound_Impl Ps (h.allFinite hlen)
  intro i hi
  obtain ⟨k, hk⟩ := h.get i hi
  exact inCoordBounds_main_of_compiled hk.h_bound

end Geometry

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

import GeometryTheorems

namespace Geometry

/-!
# Mutation proofs for `geometry`

The first two theorems show that the preconditions of the compiled refinement theorems (`InRange` and
`PathInRange`) hold for real calls, so those theorems are not vacuous. Each mutant after them is a plausible
buggy variant of the compiled ray march `rayMarchSegmentCoords`; for each one, we prove that it violates the
property the corresponding master theorem in `GeometryTheorems.lean` proves for the real march.
-/

/-- A horizontal segment ten cells long, marched as `cellIntersections` in `LineSegment.kt` marches it. -/
theorem inRange_sample :
    InRange ⟨0.5, 0.5⟩ ⟨10.5, 0.5⟩ 0.5 0.5 10.5 0.5 0 0 10 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold Point32.isFinite) <;> (try unfold inCoordBounds) <;> decide +kernel

/-- A two-segment polyline, marched segment by segment as `cellIntersections(points)` marches it. -/
theorem pathInRange_sample :
    PathInRange [⟨0.5, 0.5⟩, ⟨10.5, 0.5⟩, ⟨10.5, 5.25⟩]
      [⟨0.5, 0.5, 10.5, 0.5, 0, 0, 10, 0⟩, ⟨10.5, 0.5, 10.5, 5.25, 10, 0, 10, 5⟩] := by
  refine ⟨?_, ?_, trivial⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold Point32.isFinite) <;> (try unfold inCoordBounds) <;>
    decide +kernel

/-- Mutant 1: a march that returns only the two endpoint cells. -/
def mutantEndpointsMarch (_sx _sy _ex _ey : Float) (cx cy ex' ey' : Int32) : Array (Int32 × Int32) :=
  #[(cx, cy), (ex', ey')]

/-- Mutant 1 violates `rayMarchSegmentCoords_hausdorff_bound`: it skips the cells between the endpoints. -/
theorem mutantEndpointsMarch_violates_hausdorff_bound :
    ¬ ∀ (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32), InRange A B sx sy ex ey cx cy ex' ey' →
      cellHausdorffDistanceLe (dedupCells (toCells (mutantEndpointsMarch sx sy ex ey cx cy ex' ey')))
        (cellIntersectionsSegment A.toPoint B.toPoint) 1 := by
  intro h
  have := (h _ _ _ _ _ _ _ _ _ _ inRange_sample).2 ⟨5, 0⟩ (by decide +kernel)
  revert this
  decide +kernel

/-- Mutant 2: a march that stops before the end cell (an off-by-one loop bound). -/
def mutantNoEndMarch (_sx _sy _ex _ey : Float) (cx cy _ex' _ey' : Int32) : Array (Int32 × Int32) :=
  #[(cx, cy)]

/-- Mutant 2 violates `rayMarchSegmentCoords_connected`: its cells cannot form a path to the end cell. -/
theorem mutantNoEndMarch_violates_connected :
    ¬ ∀ (A B : Point32) (sx sy ex ey : Float) (cx cy ex' ey' : Int32), InRange A B sx sy ex ey cx cy ex' ey' →
      ∃ path : List Cell, path.head? = some (floorPoint32 A) ∧ path.getLast? = some (floorPoint32 B) ∧
        CellPathConnected path ∧
        ∀ c, c ∈ path ↔ c ∈ toCells (mutantNoEndMarch sx sy ex ey cx cy ex' ey') := by
  intro h
  obtain ⟨path, _, hlast, _, hmem⟩ := h _ _ _ _ _ _ _ _ _ _ inRange_sample
  have hend : floorPoint32 ⟨10.5, 0.5⟩ ∈ path := List.mem_of_getLast? hlast
  have := (hmem _).mp hend
  revert this
  decide +kernel

end Geometry

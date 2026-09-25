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
import Geometry.FloatModel
import Geometry.FloatSemantics
import Geometry.LineSegment
import Geometry.RayMarchStep
import Mathlib.Tactic.Linarith

namespace Geometry

/--
The next cell produced by `rayMarchStepFloat` is always one of the 4 candidate transitions:
current cell, stepX neighbor, stepY neighbor, or diagonal step.
-/
theorem rayMarchStepFloat_candidates (start : Point32) (dx dy : Binary32) (stepX stepY : Int) (c : Cell) :
    (rayMarchStepFloat start dx dy stepX stepY c).1 ∈ [
      c,
      ⟨c.x + stepX, c.y⟩,
      ⟨c.x, c.y + stepY⟩,
      ⟨c.x + stepX, c.y + stepY⟩
    ] := by
  unfold rayMarchStepFloat
  dsimp only []
  by_cases hx0 : stepX == 0
  · simp only [hx0, ite_true]
    split_ifs <;> simp
  · simp only [hx0, Bool.false_eq_true, ite_false]
    by_cases hy0 : stepY == 0
    · simp only [hy0, ite_true]
      split_ifs <;> simp
    · simp only [hy0, Bool.false_eq_true, ite_false]
      split_ifs <;> simp

/--
Every step taken in floating-point raymarching changes coordinates by at most 1 in Chebyshev distance
relative to the current cell, ensuring path continuity.
-/
theorem chebyshevDistance_stepFloat_le_one (start : Point32) (dx dy : Binary32) (stepX stepY : Int)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1) (c : Cell) :
    chebyshevDistance c (rayMarchStepFloat start dx dy stepX stepY c).1 ≤ 1 := by
  have hc := rayMarchStepFloat_candidates start dx dy stepX stepY c
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h
  · rw [h]
    unfold chebyshevDistance
    simp
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hX with rfl | rfl | rfl <;> omega
  · rw [h]
    unfold chebyshevDistance
    simp only [sub_self, Int.natAbs_zero]
    rcases hY with rfl | rfl | rfl <;> omega
  · rw [h]
    have hx : c.x - (⟨c.x + stepX, c.y + stepY⟩ : Cell).x = -stepX := by simp
    have hy : c.y - (⟨c.x + stepX, c.y + stepY⟩ : Cell).y = -stepY := by simp
    unfold chebyshevDistance
    rw [hx, hy]
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;> omega

/--
Helper lemma bounding Chebyshev distance between any two candidate cell displacements.
-/
theorem chebyshevDistance_candidate_cells_le_one (c : Cell) (stepX stepY : Int)
    (hX : stepX = -1 ∨ stepX = 0 ∨ stepX = 1) (hY : stepY = -1 ∨ stepY = 0 ∨ stepY = 1)
    (dx1 dy1 dx2 dy2 : Int)
    (hx1 : dx1 = 0 ∨ dx1 = stepX) (hy1 : dy1 = 0 ∨ dy1 = stepY)
    (hx2 : dx2 = 0 ∨ dx2 = stepX) (hy2 : dy2 = 0 ∨ dy2 = stepY) :
    chebyshevDistance ⟨c.x + dx1, c.y + dy1⟩ ⟨c.x + dx2, c.y + dy2⟩ ≤ 1 := by
  have hx : (⟨c.x + dx1, c.y + dy1⟩ : Cell).x - (⟨c.x + dx2, c.y + dy2⟩ : Cell).x = dx1 - dx2 := by simp
  have hy : (⟨c.x + dx1, c.y + dy1⟩ : Cell).y - (⟨c.x + dx2, c.y + dy2⟩ : Cell).y = dy1 - dy2 := by simp
  unfold chebyshevDistance
  rw [hx, hy]
  rcases hx1 with rfl | rfl <;>
    rcases hx2 with rfl | rfl <;>
    rcases hy1 with rfl | rfl <;>
    rcases hy2 with rfl | rfl <;>
    rcases hX with rfl | rfl | rfl <;>
    rcases hY with rfl | rfl | rfl <;>
    omega

end Geometry

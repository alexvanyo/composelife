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
import Geometry.LineSegment
import Geometry.FloatModel
import GeometryDefs
import FloatLib
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry

open FloatLib.Floats

theorem eps32_pos : 0 < eps32 := by
  change 0 < (1 : ℚ) / (2^24)
  positivity

theorem eps64_pos : 0 < eps64 := by
  change 0 < (1 : ℚ) / (2^53)
  positivity

/--
Monotonicity of inCoordBounds: bounds transfer to any larger bound.
-/
theorem inCoordBounds_le {M1 M2 : ℚ} (hM : M1 ≤ M2) {A B : Point} (h : inCoordBounds M1 A B) :
    inCoordBounds M2 A B := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨le_trans h1 hM, le_trans h2 hM, le_trans h3 hM, le_trans h4 hM⟩

theorem gammaBound_nonneg (M : ℚ) (hM : 0 ≤ M) : 0 ≤ gammaBound M := by
  unfold gammaBound
  have h1 : 0 ≤ 8 * M * M + 8 * M := by
    have h2 : 0 ≤ 8 * M * M := by positivity
    have h3 : 0 ≤ 8 * M := by positivity
    linarith
  have h_eps : 0 ≤ eps32 := le_of_lt eps32_pos
  positivity

/--
The cross-product discrepancy bound at coordinate scale M = mainCoordBound is strictly less than 1.
-/
theorem gammaBound_mainCoordBound_lt_one : gammaBound mainCoordBound < 1 := by
  unfold gammaBound eps32 mainCoordBound
  norm_num

/--
The cross-product discrepancy bound at coordinate scale M = 1447 is strictly less than 1.
-/
theorem gammaBound_1447_lt_one : gammaBound 1447 < 1 := by
  unfold gammaBound eps32
  norm_num

end Geometry

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
import FloatLib
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry

open FloatLib.Floats



/--
Machine epsilon for IEEE-754 single-precision (binary32) floats: 2^(-24).
-/
def eps32 : ℚ := 1 / (2^24)

/--
Machine epsilon for IEEE-754 double-precision (binary64) floats: 2^(-53).
-/
def eps64 : ℚ := 1 / (2^53)

theorem eps32_pos : 0 < eps32 := by
  change 0 < (1 : ℚ) / (2^24)
  positivity

theorem eps64_pos : 0 < eps64 := by
  change 0 < (1 : ℚ) / (2^53)
  positivity

/--
Coordinate size bound condition: coordinates are bounded in magnitude by M.
-/
def inCoordBounds (M : ℚ) (A B : Point) : Prop :=
  |A.x| ≤ M ∧ |A.y| ≤ M ∧ |B.x| ≤ M ∧ |B.y| ≤ M

/--
Monotonicity of inCoordBounds: bounds transfer to any larger bound.
-/
theorem inCoordBounds_le {M1 M2 : ℚ} (hM : M1 ≤ M2) {A B : Point} (h : inCoordBounds M1 A B) :
    inCoordBounds M2 A B := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨le_trans h1 hM, le_trans h2 hM, le_trans h3 hM, le_trans h4 hM⟩

/--
Upper bound on the cross-product decision discrepancy between floating point
and exact rational arithmetic for coordinates within [-M, M].
γ(M) = eps32 * (8 * M^2 + 8 * M).
-/
def gammaBound (M : ℚ) : ℚ :=
  eps32 * (8 * M * M + 8 * M)

theorem gammaBound_nonneg (M : ℚ) (hM : 0 ≤ M) : 0 ≤ gammaBound M := by
  unfold gammaBound
  have h1 : 0 ≤ 8 * M * M + 8 * M := by
    have h2 : 0 ≤ 8 * M * M := by positivity
    have h3 : 0 ≤ 8 * M := by positivity
    linarith
  have h_eps : 0 ≤ eps32 := le_of_lt eps32_pos
  positivity

/--
The cross-product discrepancy bound at coordinate scale M = 1000 is strictly less than 1.
-/
theorem gammaBound_1000_lt_one : gammaBound 1000 < 1 := by
  unfold gammaBound eps32
  norm_num

/--
The cross-product discrepancy bound at coordinate scale M = 1447 is strictly less than 1.
-/
theorem gammaBound_1447_lt_one : gammaBound 1447 < 1 := by
  unfold gammaBound eps32
  norm_num

/--
Evaluates the ideal continuous cross-product difference between a line segment AB
and an integer cell corner boundary (xb, yb).
-/
def idealCrossCorner (A B : Point) (xb yb : ℚ) : ℚ :=
  let dx := B.x - A.x
  let dy := B.y - A.y
  let absDx := if dx ≥ 0 then dx else -dx
  let absDy := if dy ≥ 0 then dy else -dy
  let remX := if xb ≥ A.x then xb - A.x else A.x - xb
  let remY := if yb ≥ A.y then yb - A.y else A.y - yb
  remX * absDy - remY * absDx

/--
A segment AB has corner clearance exceeding gammaBound M and step agreement between
the floating-point and idealized raymarching transitions, ensuring that
finite precision rounding does not alter the discrete cell traversal.
-/
def HasCornerClearance (A B : Point) (M : ℚ) : Prop :=
  (∀ xb yb : ℤ,
    |idealCrossCorner A B (ofInt xb) (ofInt yb)| > gammaBound M ∨
    idealCrossCorner A B (ofInt xb) (ofInt yb) = 0) ∧
  (∀ (A' B' : Point32), A'.toPoint = A → B'.toPoint = B →
    (if B'.x - A'.x > 0.0 then 1 else if B'.x - A'.x < 0.0 then -1 else 0) =
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0) ∧
    (if B'.y - A'.y > 0.0 then 1 else if B'.y - A'.y < 0.0 then -1 else 0) =
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) ∧
    (∀ c, rayMarchStepFloat A' (B'.x - A'.x) (B'.y - A'.y)
      (if B'.x - A'.x > 0.0 then 1 else if B'.x - A'.x < 0.0 then -1 else 0)
      (if B'.y - A'.y > 0.0 then 1 else if B'.y - A'.y < 0.0 then -1 else 0) c =
      rayMarchStep A B (B.x - A.x) (B.y - A.y)
      (if B.x - A.x > 0 then 1 else if B.x - A.x < 0 then -1 else 0)
      (if B.y - A.y > 0 then 1 else if B.y - A.y < 0 then -1 else 0) c))

end Geometry


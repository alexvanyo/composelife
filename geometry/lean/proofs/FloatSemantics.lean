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
The cross-product discrepancy bound at coordinate scale M = clearanceCoordBound is strictly less than 1.
-/
theorem gammaBound_clearanceCoordBound_lt_one : gammaBound clearanceCoordBound < 1 := by
  unfold gammaBound eps32 clearanceCoordBound clearanceCoordBoundNat
  norm_num

/--
The cross-product discrepancy bound at coordinate scale M = 1447 is strictly less than 1.
-/
theorem gammaBound_1447_lt_one : gammaBound 1447 < 1 := by
  unfold gammaBound eps32
  norm_num

/--
Counterexample: at scale M = 1448, the cross-product discrepancy bound fails (gammaBound 1448 ≥ 1).
-/
theorem gammaBound_1448_ge_one : gammaBound 1448 ≥ 1 := by
  unfold gammaBound eps32
  norm_num

/--
The maximum cell boundary distance is strictly within the 24-bit single-precision mantissa capacity (2^24).
-/
theorem maxCellBoundaryDistance_lt_2_pow_24_rat : maxCellBoundaryDistance < 16777216 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
The maximum cell boundary distance is strictly within the 24-bit single-precision mantissa capacity (2^24).
-/
theorem maxCellBoundaryDistance_lt_2_pow_24 : (maxCellBoundaryDistance : ℝ) < 16777216 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
The maximum coordinate span is strictly within the 24-bit single-precision mantissa capacity (2^24).
-/
theorem maxCoordDelta_lt_2_pow_24_rat : maxCoordDelta < 16777216 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
The maximum coordinate span is strictly within the 24-bit single-precision mantissa capacity (2^24).
-/
theorem maxCoordDelta_lt_2_pow_24 : (maxCoordDelta : ℝ) < 16777216 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
The maximum relative error on cell boundary distances is at most 1/4 (rational).
-/
theorem maxCellBoundaryDistance_mul_eps_le_quarter_rat : (1 / 16777216 : ℚ) * maxCellBoundaryDistance ≤ 1/4 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
The maximum relative error on cell boundary distances is at most 1/4.
-/
theorem maxCellBoundaryDistance_mul_eps_le_quarter : (1 / 16777216 : ℝ) * (maxCellBoundaryDistance : ℝ) ≤ 1/4 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
The maximum relative error on coordinate spans is at most 1/4 (rational).
-/
theorem maxCoordDelta_mul_eps_le_quarter_rat : (1 / 16777216 : ℚ) * maxCoordDelta ≤ 1/4 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
The maximum relative error on coordinate spans is at most 1/4.
-/
theorem maxCoordDelta_mul_eps_le_quarter : (1 / 16777216 : ℝ) * (maxCoordDelta : ℝ) ≤ 1/4 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
Real casting of maxCoordDelta matches 2 * mainCoordBound.
-/
theorem maxCoordDelta_eq_two_mul : (maxCoordDelta : ℝ) = 2 * (mainCoordBound : ℝ) := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBound
  push_cast
  rfl

/--
Real casting of maxCellBoundaryDistance matches 2 * mainCoordBound + 2.
-/
theorem maxCellBoundaryDistance_eq : (maxCellBoundaryDistance : ℝ) = 2 * (mainCoordBound : ℝ) + 2 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBound
  push_cast
  rfl

/--
maxCoordDelta is bounded by maxCellBoundaryDistance.
-/
theorem maxCoordDelta_le_maxCellBoundaryDistance : (maxCoordDelta : ℝ) ≤ (maxCellBoundaryDistance : ℝ) := by
  unfold maxCoordDelta maxCoordDeltaNat maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
Evaluated numeral value of maxCoordDelta in ℝ (2 * mainCoordBoundNat = 2,097,150) for linear arithmetic.
-/
theorem maxCoordDelta_toReal_eval : (maxCoordDelta : ℝ) = 2097150 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
Evaluated numeral value of maxCellBoundaryDistance in ℝ (2 * mainCoordBoundNat + 2 = 2,097,152) for linear arithmetic.
-/
theorem maxCellBoundaryDistance_toReal_eval : (maxCellBoundaryDistance : ℝ) = 2097152 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
Evaluated rational numeral of epsRayMarch in ℝ for linear arithmetic.
-/
theorem epsRayMarch_toReal_eval :
    (epsRayMarch : ℝ) = 302231464192331558682625 / 2535301200456458802993406410752 := by
  unfold epsRayMarch eps32 eps64
  push_cast
  ring

/--
The ray march cross-product relative error bound is strictly positive.
-/
theorem epsRayMarch_pos : 0 < epsRayMarch := by
  unfold epsRayMarch eps32 eps64
  norm_num

end Geometry

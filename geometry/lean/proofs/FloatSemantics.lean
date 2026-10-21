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
import FloatLib
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Geometry

open FloatLib.Floats

theorem epsRayMarch_pos : 0 < epsRayMarch := by
  unfold epsRayMarch eps64
  norm_num

/--
The maximum relative error on cell boundary distances is at most 1/4.
-/
theorem maxCellBoundaryDistance_mul_eps_le_quarter :
    (1 / 9007199254740992 : ℝ) * (maxCellBoundaryDistance : ℝ) ≤ 1/4 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
The maximum relative error on coordinate spans is at most 1/4.
-/
theorem maxCoordDelta_mul_eps_le_quarter : (1 / 9007199254740992 : ℝ) * (maxCoordDelta : ℝ) ≤ 1/4 := by
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
Evaluated numeral value of maxCoordDelta in ℝ (2 * mainCoordBoundNat = 4,294,967,290) for linear arithmetic.
-/
theorem maxCoordDelta_toReal_eval : (maxCoordDelta : ℝ) = 4294967290 := by
  unfold maxCoordDelta maxCoordDeltaNat mainCoordBoundNat
  norm_num

/--
Evaluated numeral value of maxCellBoundaryDistance in ℝ (2 * mainCoordBoundNat + 2 = 4,294,967,292)
for linear arithmetic.
-/
theorem maxCellBoundaryDistance_toReal_eval : (maxCellBoundaryDistance : ℝ) = 4294967292 := by
  unfold maxCellBoundaryDistance maxCellBoundaryDistanceNat mainCoordBoundNat
  norm_num

/--
Evaluated rational numeral of epsRayMarch in ℝ for linear arithmetic.
-/
theorem epsRayMarch_toReal_eval :
    (epsRayMarch : ℝ) = 243388915243820072108964779655169 / 730750818665451459101842416358141509827966271488 := by
  unfold epsRayMarch eps64
  push_cast
  ring

end Geometry

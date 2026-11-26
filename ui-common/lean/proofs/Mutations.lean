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

import models.TargetStateModel
import models.EasingPiecewiseModel

namespace UiCommon.Mutations

open UiCommon.Model

/-! ### Area 7 (`TargetState`) Non-Vacuity & Mutant Checks -/

/-- Non-vacuity: `mkInProgress?` constructs a valid `InProgress` state for distinct values. -/
theorem mkInProgress?_nonvacuous :
    ∃ s : TargetState Bool Unit,
      TargetState.mkInProgress? true false (0.25 : Float32) () = some s ∧ s.IsValid := by
  refine ⟨.inProgress true false (0.25 : Float32) (), ?_, ?_⟩
  · simp [TargetState.mkInProgress?]
  · simp [TargetState.IsValid]

/-- Non-vacuity: dyadic `0.25f` satisfies `1.0f - (1.0f - pr) = pr` in IEEE-754 `Float32`. -/
theorem progressToTrue_not_dyadic_nonvacuous :
    (TargetState.inProgress (μ := Unit) true false (0.25 : Float32) ()).not.progressToTrue =
      (1.0 : Float32) -
        (TargetState.inProgress (μ := Unit) true false (0.25 : Float32) ()).progressToTrue := by
  decide

/--
Mutant check: IEEE-754 `Float32` subtraction roundoff breaks `1f - (1f - pr) = pr` for `pr = 0.0001f`,
justifying the explicit involution hypothesis in `progressToTrue_not_exact_when_involution`.
-/
theorem mutantFloat32_roundoff_breaks_involution :
    let pr := Float32.ofBits 0x38d1b717
    (TargetState.inProgress (μ := Unit) true false pr ()).not.progressToTrue ≠
      (1.0 : Float32) -
        (TargetState.inProgress (μ := Unit) true false pr ()).progressToTrue := by
  decide

/-- Mutant: omitting `require(current != provisional)` produces an invalid `InProgress` state. -/
def mutantUncheckedInProgress {α μ : Type} (c p : α) (pr : Float32) (m : μ) : TargetState α μ :=
  .inProgress c p pr m

theorem mutantUncheckedInProgress_violates_invariant :
    ¬ (mutantUncheckedInProgress true true (0.5 : Float32) ()).IsValid := by
  simp [mutantUncheckedInProgress, TargetState.IsValid]

/-! ### Area 8 (`EasingPiecewise`) Non-Vacuity & Mutant Checks -/

/-- Non-vacuity: valid `(0f, 1f)` keyframes pass validation and yield a strictly positive span. -/
theorem piecewiseSegment_valid_nonvacuous :
    ∃ keys es,
      validateEasingKeyframes "e0" [((0.25 : Float32), "e1"), ((0.75 : Float32), "e2")] =
        some (keys, es) ∧
      piecewiseSegment keys es (0.5 : Float32) =
        some ("e1", (0.25 : Float32), (0.75 : Float32)) ∧
      floatCompareLt (0.25 : Float32) (0.75 : Float32) = true := by
  refine ⟨[(0.0 : Float32), (0.25 : Float32), (0.75 : Float32)], ["e0", "e1", "e2"], ?_, ?_, ?_⟩
  · simp [validateEasingKeyframes, isSortedByKeyframe, floatCompareLe,
      buildKeyframeMap, putKeyMap, floatKeyEq]
    decide
  · simp [piecewiseSegment, floorBinarySearch, floorBinarySearchFuel, floorBinarySearchLoop]
    decide
  · decide

/-- Mutant: unsorted keyframes are rejected by `validateEasingKeyframes`. -/
theorem mutantUnsortedKeyframes_rejected :
    validateEasingKeyframes "e0" [((0.75 : Float32), "e1"), ((0.25 : Float32), "e2")] = none := by
  simp [validateEasingKeyframes, isSortedByKeyframe, floatCompareLe]
  decide

/-- Mutant: duplicate `0.0f` keyframe is rejected by `validateEasingKeyframes`. -/
theorem mutantDuplicateZeroKeyframe_rejected :
    validateEasingKeyframes "e0" [((0.0 : Float32), "e1")] = none := by
  simp [validateEasingKeyframes, isSortedByKeyframe, buildKeyframeMap, putKeyMap, floatKeyEq]

/-- Mutant: omitting the `k < 1.0f` keyframe upper bound allows a zero-width final segment `1.0f - 1.0f = 0.0f`. -/
theorem mutantBoundaryKeyframe1_zero_denom :
    piecewiseSegment [(0.0 : Float32), (1.0 : Float32)] ["e0", "e1"] (1.0 : Float32) =
      some ("e1", (1.0 : Float32), (1.0 : Float32)) := by
  simp [piecewiseSegment, floorBinarySearch, floorBinarySearchFuel, floorBinarySearchLoop]
  decide

/-- Negative input `t < 0.0f` returns `-1` from `floorBinarySearch` and traps in `piecewiseSegment`. -/
theorem negativeInput_traps_piecewiseSegment :
    floorBinarySearch [(0.0 : Float32), (0.5 : Float32)] (-0.25 : Float32) = -1 ∧
    piecewiseSegment [(0.0 : Float32), (0.5 : Float32)] ["e0", "e1"] (-0.25 : Float32) = none := by
  simp [piecewiseSegment, floorBinarySearch]
  decide

end UiCommon.Mutations

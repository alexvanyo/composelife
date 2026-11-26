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

import proofs.EasingPiecewiseModelProofs

namespace UiCommon.Model

theorem floorBinarySearchLoop_readsInBounds (keys : List Float32) (value : Float32)
    (low high fuel : Nat) (hlo : low < high) (hhi : high ≤ keys.length) :
    FloorSearchReadsInBounds keys value low high fuel :=
  floorBinarySearchLoop_readsInBounds_Impl keys value low high fuel hlo hhi

theorem floorBinarySearchLoop_terminates_in_log (keys : List Float32) (value : Float32)
    (low high fuel : Nat) (hlo : low < high) (hhi : high ≤ keys.length)
    (hf : floorBinarySearchFuel keys.length ≤ fuel) :
    floorBinarySearchLoop keys value low high fuel =
      floorBinarySearchLoop keys value low high (floorBinarySearchFuel keys.length) :=
  floorBinarySearchLoop_terminates_in_log_Impl keys value low high fuel hlo hhi hf

theorem floorBinarySearch_neg_one_iff (keys : List Float32) (value : Float32)
    (hne : 0 < keys.length) :
    floorBinarySearch keys value = -1 ↔ floatCompare value keys[0] < 0 :=
  floorBinarySearch_neg_one_iff_Impl keys value hne

theorem floorBinarySearch_nonneg_bounds (keys : List Float32) (value : Float32)
    (hne : 0 < keys.length) (hge : ¬ floatCompare value keys[0] < 0) :
    ∃ i : Nat,
      floorBinarySearch keys value = (i : Int) ∧
      i < keys.length ∧
      floatCompare keys[i]! value ≤ 0 ∧
      (i + 1 = keys.length ∨ (i + 1 < keys.length ∧ floatCompare value keys[i + 1]! < 0)) :=
  floorBinarySearch_nonneg_bounds_Impl keys value hne hge

theorem validateEasingKeyframes_strict_increasing {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E)
    (hval : validateEasingKeyframes easing easings = some (keys, es)) :
    keys = (0.0 : Float32) :: easings.map Prod.fst ∧
      es = easing :: easings.map Prod.snd ∧
      keys.length = es.length ∧
      0 < keys.length ∧
      KeysStrictlyIncreasing (easings.map Prod.fst) ∧
      (∀ k ∈ easings.map Prod.fst, floatKeyEq (0.0 : Float32) k = false) :=
  validateEasingKeyframes_strict_increasing_Impl easing easings keys es hval

theorem piecewiseSegment_valid_nonzero_denom {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E) (t : Float32)
    (hval : validateEasingKeyframes easing easings = some (keys, es))
    (hunitInterval : ∀ k ∈ easings.map Prod.fst,
      floatCompareLt (0.0 : Float32) k = true ∧ floatCompareLt k (1.0 : Float32) = true)
    (ht : floatCompare (0.0 : Float32) t ≤ 0) :
    ∃ e pStart pEnd,
      piecewiseSegment keys es t = some (e, pStart, pEnd) ∧
      floatCompareLt pStart pEnd = true ∧
      floatKeyEq pStart pEnd = false :=
  piecewiseSegment_valid_nonzero_denom_Impl easing easings keys es t hval hunitInterval ht

theorem piecewiseSegment_interior_nonzero_denom {E : Type}
    (easing : E) (easings : List (Float32 × E))
    (keys : List Float32) (es : List E) (t : Float32) (i : Nat)
    (hval : validateEasingKeyframes easing easings = some (keys, es))
    (hidx : floorBinarySearch keys t = (i : Int))
    (hposIdx : 0 < i) (hltNext : i + 1 < keys.length) :
    ∃ e pStart pEnd,
      piecewiseSegment keys es t = some (e, pStart, pEnd) ∧
      floatCompareLt pStart pEnd = true ∧
      floatKeyEq pStart pEnd = false :=
  piecewiseSegment_interior_nonzero_denom_Impl easing easings keys es t i hval hidx hposIdx hltNext

end UiCommon.Model

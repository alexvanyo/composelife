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

import models.ViewportMathModel

namespace UiCells.Model

theorem gridAnchor_roundtrip_Impl (origin scale anchor : Int) (hpos : scale ≠ 0) :
    gridAnchorClosest origin scale (gridAnchorPos origin scale anchor) = anchor := by
  unfold gridAnchorClosest gridAnchorPos
  rw [Int.mul_ediv_cancel _ hpos]
  omega

theorem setScaleRange_empty_none_Impl (curScale : Float32) (r : FloatRangeModel)
    (hemp : r.isEmpty = true) :
    setScaleRangeModel curScale r = none := by
  simp [setScaleRangeModel, hemp]

theorem setScaleRange_nonempty_some_Impl (curScale : Float32) (r : FloatRangeModel)
    (hne : r.isEmpty = false) :
    setScaleRangeModel curScale r = some (r, coerceInFloatRange curScale r) := by
  simp [setScaleRangeModel, hne]

end UiCells.Model

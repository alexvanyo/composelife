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

import models.UiUtilModel

namespace UiCommon.KotlinModel

theorem nonNegativeLongShouldRevert_empty_Impl (p : Option Int64) :
    nonNegativeLongShouldRevert true p = false := rfl

theorem nonNegativeLongShouldRevert_none_Impl :
    nonNegativeLongShouldRevert false none = true := rfl

theorem nonNegativeLongShouldRevert_nonneg_Impl (v : Int64) (hv : ¬ (v < 0)) :
    nonNegativeLongShouldRevert false (some v) = false := by
  simp [nonNegativeLongShouldRevert, hv]

theorem nonNegativeDoubleShouldRevert_empty_Impl (p : Option Float) :
    nonNegativeDoubleShouldRevert true p = false := rfl

theorem nonNegativeDoubleShouldRevert_nan_Impl (d : Float) (hnan : d.isNaN = true) :
    nonNegativeDoubleShouldRevert false (some d) = true := by
  simp [nonNegativeDoubleShouldRevert, hnan]

end UiCommon.KotlinModel

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
import proofs.UiUtilModelProofs

namespace UiCommon.KotlinModel

theorem nonNegativeLongShouldRevert_empty (p : Option Int64) :
    nonNegativeLongShouldRevert true p = false :=
  nonNegativeLongShouldRevert_empty_Impl p

theorem nonNegativeLongShouldRevert_none :
    nonNegativeLongShouldRevert false none = true :=
  nonNegativeLongShouldRevert_none_Impl

theorem nonNegativeLongShouldRevert_nonneg (v : Int64) (hv : ¬ (v < 0)) :
    nonNegativeLongShouldRevert false (some v) = false :=
  nonNegativeLongShouldRevert_nonneg_Impl v hv

theorem nonNegativeDoubleShouldRevert_empty (p : Option Float) :
    nonNegativeDoubleShouldRevert true p = false :=
  nonNegativeDoubleShouldRevert_empty_Impl p

theorem nonNegativeDoubleShouldRevert_nan (d : Float) (hnan : d.isNaN = true) :
    nonNegativeDoubleShouldRevert false (some d) = true :=
  nonNegativeDoubleShouldRevert_nan_Impl d hnan

end UiCommon.KotlinModel

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

import theorems.ViewportMathModelTheorems

namespace UiCells.Model

/-- Mutant modeling the pre-fix bug (`require(!oldRange.isEmpty())` instead of `require(!newRange.isEmpty())`). -/
def mutantSetScaleRangeChecksOld (oldRange : FloatRangeModel) (curScale : Float32)
    (newRange : FloatRangeModel) : Option (FloatRangeModel × Float32) :=
  if oldRange.isEmpty then none
  else some (newRange, coerceInFloatRange curScale newRange)

theorem mutantSetScaleRangeChecksOld_violates_empty_rejection :
    let validOld : FloatRangeModel := { lo := (0.5 : Float32), hi := (2.0 : Float32) }
    let emptyNew : FloatRangeModel := { lo := (2.0 : Float32), hi := (0.5 : Float32) }
    emptyNew.isEmpty = true ∧ mutantSetScaleRangeChecksOld validOld (1.0 : Float32) emptyNew ≠ none := by
  decide

end UiCells.Model

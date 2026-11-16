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

import models.CalculatorModel

namespace MosaicCalculator.Mutations

open MosaicCalculator.Model

/-- Non-vacuity check: small non-negative inputs satisfy `checkedAddModel_nonneg_small`'s preconditions. -/
theorem checkedAddModel_nonneg_small_nonvacuous :
    ∃ a b : Int64, (0 ≤ a.toInt ∧ a.toInt ≤ 1000000) ∧ (0 ≤ b.toInt ∧ b.toInt ≤ 1000000) ∧
      checkedAddModel a b = .value (Int64.ofInt (a.toInt + b.toInt)) := by
  refine ⟨12, 30, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Mutant: omitting the division-by-zero check fails `reduceCalculatorState_divZero_enters_error`. -/
def mutantDivZero (lhs : Int64) : CheckedEvalResult :=
  .value (jvmI64Div lhs 0)

theorem mutantDivZero_violates_error :
    mutantDivZero 42 ≠ .error .divideByZero := by
  decide +kernel

end MosaicCalculator.Mutations

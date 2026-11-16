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

import proofs.CalculatorModelProofs

namespace MosaicCalculator.Model

theorem reduceCalculatorState_clear_resets (st : CalculatorState) :
    reduceCalculatorStateModel st .clear = CalculatorState.initial :=
  reduceCalculatorState_clear_resets_Impl st

theorem reduceCalculatorState_divZero_enters_error (lhs : Int64) :
    reduceCalculatorStateModel
      { displayValue := 0, pendingOperand := some lhs, pendingOp := some .div, enteringNewNumber := false, error := none }
      .equals = { error := some .divideByZero } :=
  reduceCalculatorState_divZero_enters_error_Impl lhs

theorem checkedAddModel_nonneg_small (a b : Int64)
    (ha : 0 ≤ a.toInt ∧ a.toInt ≤ 1000000) (hb : 0 ≤ b.toInt ∧ b.toInt ≤ 1000000) :
    checkedAddModel a b = .value (Int64.ofInt (a.toInt + b.toInt)) :=
  checkedAddModel_nonneg_small_Impl a b ha hb

theorem expectedCalculatorScreen_has_six_lines (st : CalculatorState) :
    (expectedCalculatorScreenLines st).length = 6 :=
  expectedCalculatorScreen_has_six_lines_Impl st

end MosaicCalculator.Model

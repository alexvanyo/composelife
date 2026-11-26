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

import models.PeriodUntilModel

namespace TimeUtil.Mutations

open TimeUtil.Model

/-- Non-vacuity check: concrete positive/negative inputs satisfy `totalNanosecondsModel_exact_bounded`. -/
theorem totalNanosecondsModel_exact_bounded_nonvacuous :
    let p : DateTimePeriodModel := { hours := 2, minutes := 30, seconds := 15, nanoseconds := 500 }
    (-(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433) ∧
    (-(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023) ∧
    (totalNanosecondsModel p).toInt =
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) := by
  decide +kernel

/-- Non-vacuity check: negative truncated division satisfies `timeComponentInWholeUnitsModel_truncation`. -/
theorem timeComponentInWholeUnitsModel_truncation_nonvacuous :
    let p : DateTimePeriodModel := { seconds := -63 }
    ∃ q, timeComponentInWholeUnitsModel p DateTimeUnit.minute = some q ∧
      q = -1 ∧ (totalNanosecondsModel p).toInt - q.toInt * DateTimeUnit.minute.nanoseconds.toInt = -3000000000 := by
  refine ⟨-1, ?_, rfl, ?_⟩ <;> decide +kernel

/-- Mutant: omitting the zero-divisor check in `timeComponentInWholeUnitsModel` fails to trap on `u = 0`. -/
def mutantNoDivZeroCheck (p : DateTimePeriodModel) (u : TimeBasedUnit) : Option Int64 :=
  some (jvmI64Div (totalNanosecondsModel p) u.nanoseconds)

theorem mutantNoDivZeroCheck_violates_trap :
    mutantNoDivZeroCheck { seconds := 5 } ⟨0⟩ ≠ none := by
  decide +kernel

/-- Mutant: omitting the `hours` term in `totalNanosecondsModel` violates the exact nanosecond identity. -/
def mutantDropHours (p : DateTimePeriodModel) : Int64 :=
  Int64.ofInt p.nanoseconds.toInt +
    (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds +
    (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds

theorem mutantDropHours_violates_exact :
    let p : DateTimePeriodModel := { hours := 1 }
    (mutantDropHours p).toInt ≠
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) := by
  decide +kernel

end TimeUtil.Mutations

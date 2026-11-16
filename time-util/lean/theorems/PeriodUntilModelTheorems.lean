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

import proofs.PeriodUntilModelProofs

namespace TimeUtil.Model

theorem totalNanosecondsModel_exact_bounded (p : DateTimePeriodModel)
    (hm : -(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433)
    (hh : -(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023)
    (hsum :
      -(2 ^ 63 : Int) ≤
        p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) ∧
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) <
        (2 ^ 63 : Int)) :
    (totalNanosecondsModel p).toInt =
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) :=
  totalNanosecondsModel_exact_bounded_Impl p hm hh hsum

theorem totalNanosecondsModel_additive (p q sum : DateTimePeriodModel)
    (hns : sum.nanoseconds.toInt = p.nanoseconds.toInt + q.nanoseconds.toInt)
    (hs : sum.seconds.toInt = p.seconds.toInt + q.seconds.toInt)
    (hm : sum.minutes.toInt = p.minutes.toInt + q.minutes.toInt)
    (hh : sum.hours.toInt = p.hours.toInt + q.hours.toInt)
    (hmp : -(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433)
    (hhp : -(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023)
    (hsump :
      -(2 ^ 63 : Int) ≤
        p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) ∧
      p.nanoseconds.toInt + 1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) <
        (2 ^ 63 : Int))
    (hmq : -(76861433 : Int) ≤ q.minutes.toInt ∧ q.minutes.toInt ≤ 76861433)
    (hhq : -(1281023 : Int) ≤ q.hours.toInt ∧ q.hours.toInt ≤ 1281023)
    (hsumq :
      -(2 ^ 63 : Int) ≤
        q.nanoseconds.toInt + 1000000000 * (q.seconds.toInt + 60 * q.minutes.toInt + 3600 * q.hours.toInt) ∧
      q.nanoseconds.toInt + 1000000000 * (q.seconds.toInt + 60 * q.minutes.toInt + 3600 * q.hours.toInt) <
        (2 ^ 63 : Int))
    (hmsum : -(76861433 : Int) ≤ sum.minutes.toInt ∧ sum.minutes.toInt ≤ 76861433)
    (hhsum : -(1281023 : Int) ≤ sum.hours.toInt ∧ sum.hours.toInt ≤ 1281023)
    (hsumsum :
      -(2 ^ 63 : Int) ≤
        sum.nanoseconds.toInt +
          1000000000 * (sum.seconds.toInt + 60 * sum.minutes.toInt + 3600 * sum.hours.toInt) ∧
      sum.nanoseconds.toInt +
          1000000000 * (sum.seconds.toInt + 60 * sum.minutes.toInt + 3600 * sum.hours.toInt) <
        (2 ^ 63 : Int)) :
    (totalNanosecondsModel sum).toInt =
      (totalNanosecondsModel p).toInt + (totalNanosecondsModel q).toInt :=
  totalNanosecondsModel_additive_Impl p q sum hns hs hm hh hmp hhp hsump hmq hhq hsumq hmsum hhsum hsumsum

theorem dateComponentInWholeUnitsModel_trap_zero (p : DateTimePeriodModel) :
    dateComponentInWholeUnitsModel p (.dayBased 0) = none ∧
    dateComponentInWholeUnitsModel p (.monthBased 0) = none :=
  dateComponentInWholeUnitsModel_trap_zero_Impl p

theorem dateComponentInWholeUnitsModel_dayBased_truncation
    (p : DateTimePeriodModel) (d : Int32) (hd : 0 < d.toInt) :
    ∃ q, dateComponentInWholeUnitsModel p (.dayBased d) = some q ∧
      let r := p.days.toInt - q.toInt * d.toInt
      q.toInt * d.toInt + r = p.days.toInt ∧
      r.natAbs < d.toInt.natAbs ∧
      (0 ≤ p.days.toInt → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (p.days.toInt ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (p.days = 0 → q = 0) :=
  dateComponentInWholeUnitsModel_dayBased_truncation_Impl p d hd

theorem dateComponentInWholeUnitsModel_monthBased_truncation
    (p : DateTimePeriodModel) (m : Int32) (hm : 0 < m.toInt) :
    ∃ q, dateComponentInWholeUnitsModel p (.monthBased m) = some q ∧
      let r := p.months.toInt - q.toInt * m.toInt
      q.toInt * m.toInt + r = p.months.toInt ∧
      r.natAbs < m.toInt.natAbs ∧
      (0 ≤ p.months.toInt → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (p.months.toInt ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (p.months = 0 → q = 0) :=
  dateComponentInWholeUnitsModel_monthBased_truncation_Impl p m hm

theorem timeComponentInWholeUnitsModel_trap_zero (p : DateTimePeriodModel) :
    timeComponentInWholeUnitsModel p ⟨0⟩ = none :=
  timeComponentInWholeUnitsModel_trap_zero_Impl p

theorem timeComponentInWholeUnitsModel_truncation
    (p : DateTimePeriodModel) (u : TimeBasedUnit) (hu : 0 < u.nanoseconds.toInt) :
    ∃ q, timeComponentInWholeUnitsModel p u = some q ∧
      let total := (totalNanosecondsModel p).toInt
      let r := total - q.toInt * u.nanoseconds.toInt
      q.toInt * u.nanoseconds.toInt + r = total ∧
      r.natAbs < u.nanoseconds.toInt.natAbs ∧
      (0 ≤ total → 0 ≤ q.toInt ∧ 0 ≤ r) ∧
      (total ≤ 0 → q.toInt ≤ 0 ∧ r ≤ 0) ∧
      (totalNanosecondsModel p = 0 → q = 0) :=
  timeComponentInWholeUnitsModel_truncation_Impl p u hu

theorem timeComponentDurationModel_nanoseconds_exact (p : DateTimePeriodModel)
    (hb : (-4611686018426999999 : Int) ≤ (totalNanosecondsModel p).toInt ∧
      (totalNanosecondsModel p).toInt ≤ 4611686018426999999) :
    (timeComponentDurationModel p).inWholeNanoseconds = totalNanosecondsModel p :=
  timeComponentDurationModel_nanoseconds_exact_Impl p hb

theorem dateComponentApproximateDurationModel_formula (p : DateTimePeriodModel) :
    dateComponentApproximateDurationModel p =
      Duration.ofLongUnit
        (Duration.plus (Duration.ofIntUnit p.days .days)
          (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).inWholeNanoseconds
        .nanoseconds :=
  dateComponentApproximateDurationModel_formula_Impl p

theorem dateComponentApproximateDurationModel_days_only (p : DateTimePeriodModel)
    (hy : p.years = 0) (hm : p.months = 0)
    (hd : (-53375 : Int) ≤ p.days.toInt ∧ p.days.toInt ≤ 53375) :
    (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt =
      p.days.toInt * 86400000000000 :=
  dateComponentApproximateDurationModel_days_only_Impl p hy hm hd

theorem approximateDurationInMinutesModel_formula (p : DateTimePeriodModel) :
    approximateDurationInMinutesModel p =
      Jvm.i64ToFloat (approximateDurationModel p).inWholeNanoseconds.toUInt64 / 60000000000.0 :=
  approximateDurationInMinutesModel_formula_Impl p

theorem approximateDurationInMinutesModel_zero :
    approximateDurationInMinutesModel {} = 0.0 :=
  approximateDurationInMinutesModel_zero_Impl

theorem approximateDurationInMinutesModel_ninety_minutes :
    (approximateDurationInMinutesModel { hours := 1, minutes := 30 }).toBits = (90.0 : Float).toBits ∧
    (approximateDurationInMinutesModel { hours := 1, minutes := 30 } == 90.0) = true :=
  approximateDurationInMinutesModel_ninety_minutes_Impl

theorem dateComponentApproximateDurationModel_inWholeNanoseconds_bounded
    (p : DateTimePeriodModel) :
    -(2 ^ 63 : Int) ≤ (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt ∧
    (dateComponentApproximateDurationModel p).inWholeNanoseconds.toInt < (2 ^ 63 : Int) :=
  dateComponentApproximateDurationModel_inWholeNanoseconds_bounded_Impl p

theorem approximateDurationModel_inWholeNanoseconds_bounded
    (p : DateTimePeriodModel) :
    -(2 ^ 63 : Int) ≤ (approximateDurationModel p).inWholeNanoseconds.toInt ∧
    (approximateDurationModel p).inWholeNanoseconds.toInt < (2 ^ 63 : Int) :=
  approximateDurationModel_inWholeNanoseconds_bounded_Impl p

end TimeUtil.Model

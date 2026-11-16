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

import Jvm.Semantics

namespace TimeUtil.Model

/-- Two's-complement signed 32-bit JVM `idiv` quotient (partial on `b = 0`). -/
def jvmI32Div (a b : Int32) : Int32 :=
  (BitVec.sdiv a.toBitVec b.toBitVec).toInt.toInt32

/-- Two's-complement signed 64-bit JVM `ldiv` quotient (partial on `b = 0`). -/
def jvmI64Div (a b : Int64) : Int64 :=
  (BitVec.sdiv a.toBitVec b.toBitVec).toInt.toInt64

/-- Clamp a signed 64-bit integer to `[lo, hi]`. -/
def clampI64 (v lo hi : Int64) : Int64 :=
  if v.toInt < lo.toInt then lo else if hi.toInt < v.toInt then hi else v

/-- Exact IEEE-754 `Math.round(double)` returning `Int64` (0 on NaN, clamped on overflow). -/
def roundDoubleToI64 (x : Float) : Int64 :=
  if x.isNaN then 0
  else if x >= 9223372036854775808.0 then (9223372036854775807 : Int64)
  else if x <= -9223372036854775808.0 then (-9223372036854775808 : Int64)
  else if x >= 4503599627370496.0 || x <= -4503599627370496.0 then
    (Jvm.floatToI64 x).toInt64
  else
    let t := (Jvm.floatToI64 x).toInt64
    let frac := x - Jvm.i64ToFloat t.toUInt64
    if x >= 0.0 then
      if frac >= 0.5 then t + 1 else t
    else
      if frac < -0.5 then t - 1 else t

/-- Standalone model of `kotlinx.datetime.DateTimePeriod` components. -/
structure DateTimePeriodModel where
  years : Int32 := 0
  months : Int32 := 0
  days : Int32 := 0
  hours : Int32 := 0
  minutes : Int32 := 0
  seconds : Int32 := 0
  nanoseconds : Int32 := 0
  deriving DecidableEq, Repr, Inhabited

/-- Construct a normalized `DateTimePeriodModel` from a total nanosecond count. -/
def DateTimePeriodModel.ofNanoseconds (totalNs : Int64) : DateTimePeriodModel :=
  let ns := totalNs.toInt
  let h := ns.tdiv 3600000000000
  let rem1 := ns.tmod 3600000000000
  let m := rem1.tdiv 60000000000
  let rem2 := rem1.tmod 60000000000
  let s := rem2.tdiv 1000000000
  let n := rem2.tmod 1000000000
  {
    hours := Int32.ofInt h
    minutes := Int32.ofInt m
    seconds := Int32.ofInt s
    nanoseconds := Int32.ofInt n
  }

/-- Construct a normalized `DateTimePeriodModel` from months (folding multiples of 12 into years). -/
def DateTimePeriodModel.ofMonths (totalMonths : Int32) : DateTimePeriodModel :=
  let m := totalMonths.toInt
  {
    years := Int32.ofInt (m.tdiv 12)
    months := Int32.ofInt (m.tmod 12)
  }

/-- Construct a `DateTimePeriodModel` from days. -/
def DateTimePeriodModel.ofDays (days : Int32) : DateTimePeriodModel :=
  { days := days }

/-- `kotlinx.datetime.DateTimeUnit.TimeBased`. -/
structure TimeBasedUnit where
  nanoseconds : Int64
  deriving DecidableEq, Repr, Inhabited

/-- `kotlinx.datetime.DateTimeUnit.DateBased` (`DayBased` or `MonthBased`). -/
inductive DateBasedUnit where
  | dayBased (days : Int32)
  | monthBased (months : Int32)
  deriving DecidableEq, Repr, Inhabited

/-- `kotlinx.datetime.DateTimeUnit` hierarchy. -/
inductive DateTimeUnit where
  | timeBased (unit : TimeBasedUnit)
  | dateBased (unit : DateBasedUnit)
  deriving DecidableEq, Repr, Inhabited

namespace DateTimeUnit

def nanosecond : TimeBasedUnit := ⟨1⟩
def microsecond : TimeBasedUnit := ⟨1000⟩
def millisecond : TimeBasedUnit := ⟨1000000⟩
def second : TimeBasedUnit := ⟨1000000000⟩
def minute : TimeBasedUnit := ⟨60000000000⟩
def hour : TimeBasedUnit := ⟨3600000000000⟩

def day : DateBasedUnit := .dayBased 1
def week : DateBasedUnit := .dayBased 7
def month : DateBasedUnit := .monthBased 1
def year : DateBasedUnit := .monthBased 12

end DateTimeUnit

/-- `kotlin.time.DurationUnit` variants used in `PeriodUntil.kt`. -/
inductive DurationUnit where
  | nanoseconds
  | microseconds
  | milliseconds
  | seconds
  | minutes
  | hours
  | days
  deriving DecidableEq, Repr, Inhabited

/-- Model of `kotlin.time.Duration` matching its packed 64-bit `rawValue` representation on JVM. -/
structure Duration where
  rawValue : Int64
  deriving DecidableEq, Repr, Inhabited

namespace Duration

def maxNanos : Int64 := (4611686018426999999 : Int64)
def maxMillis : Int64 := (4611686018427387903 : Int64)
def maxNanosInMillis : Int64 := (4611686018426 : Int64)
def zero : Duration := ⟨0⟩
def infinite : Duration := ⟨((maxMillis.toUInt64 <<< 1) + 1).toInt64⟩
def negInfinite : Duration := ⟨(((-maxMillis).toUInt64 <<< 1) + 1).toInt64⟩

def ofNanos (ns : Int64) : Duration :=
  ⟨(ns.toUInt64 <<< 1).toInt64⟩

def ofMillis (ms : Int64) : Duration :=
  ⟨((ms.toUInt64 <<< 1) + 1).toInt64⟩

def isInNanos (d : Duration) : Bool :=
  (d.rawValue.toUInt64 &&& 1) == 0

def rawUnits (d : Duration) : Int64 :=
  (d.rawValue.toBitVec.sshiftRight 1).toInt.toInt64

def isInfinite (d : Duration) : Bool :=
  !d.isInNanos && (d.rawUnits == maxMillis || d.rawUnits == -maxMillis)

def ofNanosNormalized (ns : Int64) : Duration :=
  if (-4611686018426999999 : Int) ≤ ns.toInt ∧ ns.toInt ≤ 4611686018426999999 then
    ofNanos ns
  else
    ofMillis (jvmI64Div ns 1000000)

def ofMillisNormalized (ms : Int64) : Duration :=
  if (-4611686018426 : Int) ≤ ms.toInt ∧ ms.toInt ≤ 4611686018426 then
    ofNanos (Int64.ofInt (ms.toInt * 1000000))
  else
    ofMillis (clampI64 ms (-maxMillis) maxMillis)

def inWholeNanoseconds (d : Duration) : Int64 :=
  if d.isInNanos then d.rawUnits
  else
    let ms := d.rawUnits.toInt
    if ms > 9223372036854 then (9223372036854775807 : Int64)
    else if ms < -9223372036854 then (-9223372036854775808 : Int64)
    else Int64.ofInt (ms * 1000000)

def ofLongUnit (v : Int64) (u : DurationUnit) : Duration :=
  let vi := v.toInt
  match u with
  | .nanoseconds => ofNanosNormalized v
  | .microseconds =>
    if (-4611686018426999 : Int) ≤ vi ∧ vi ≤ 4611686018426999 then
      ofNanos (Int64.ofInt (vi * 1000))
    else
      ofMillis (clampI64 (jvmI64Div v 1000) (-maxMillis) maxMillis)
  | .milliseconds => ofMillisNormalized v
  | .seconds =>
    if (-4611686018 : Int) ≤ vi ∧ vi ≤ 4611686018 then
      ofNanos (Int64.ofInt (vi * 1000000000))
    else
      let ms :=
        if vi > 4611686018427387 then maxMillis
        else if vi < -4611686018427387 then -maxMillis
        else Int64.ofInt (vi * 1000)
      ofMillis (clampI64 ms (-maxMillis) maxMillis)
  | .minutes =>
    if (-76861433 : Int) ≤ vi ∧ vi ≤ 76861433 then
      ofNanos (Int64.ofInt (vi * 60000000000))
    else
      let ms :=
        if vi > 76861433640456 then maxMillis
        else if vi < -76861433640456 then -maxMillis
        else Int64.ofInt (vi * 60000)
      ofMillis (clampI64 ms (-maxMillis) maxMillis)
  | .hours =>
    if (-1281023 : Int) ≤ vi ∧ vi ≤ 1281023 then
      ofNanos (Int64.ofInt (vi * 3600000000000))
    else
      let ms :=
        if vi > 1281023894007 then maxMillis
        else if vi < -1281023894007 then -maxMillis
        else Int64.ofInt (vi * 3600000)
      ofMillis (clampI64 ms (-maxMillis) maxMillis)
  | .days =>
    if (-53375 : Int) ≤ vi ∧ vi ≤ 53375 then
      ofNanos (Int64.ofInt (vi * 86400000000000))
    else
      let ms :=
        if vi > 53375995583 then maxMillis
        else if vi < -53375995583 then -maxMillis
        else Int64.ofInt (vi * 86400000)
      ofMillis (clampI64 ms (-maxMillis) maxMillis)

def ofIntUnit (v : Int32) (u : DurationUnit) : Duration :=
  ofLongUnit (Int64.ofInt v.toInt) u

def ofDaysFloat? (days : Float) : Option Duration :=
  let nsFloat := days * 86400000000000.0
  if nsFloat.isNaN then none
  else
    let ns := roundDoubleToI64 nsFloat
    if (-4611686018426999999 : Int) ≤ ns.toInt ∧ ns.toInt ≤ 4611686018426999999 then
      some (ofNanos ns)
    else
      let ms := roundDoubleToI64 (days * 86400000.0)
      some (ofMillisNormalized ms)

def ofDaysFloat (days : Float) : Duration :=
  (ofDaysFloat? days).getD zero

private def addMixed (n m : Int64) : Duration :=
  if m == maxMillis || m == -maxMillis then ofMillis m
  else
    let nMs := jvmI64Div n 1000000
    let nRem := n.toInt - nMs.toInt * 1000000
    let sumMs := m.toInt + nMs.toInt
    if (-4611686018426 : Int) ≤ sumMs ∧ sumMs ≤ 4611686018426 then
      ofNanosNormalized (Int64.ofInt (sumMs * 1000000 + nRem))
    else
      let clamped :=
        if sumMs > 4611686018427387903 then maxMillis
        else if sumMs < -4611686018427387903 then -maxMillis
        else Int64.ofInt sumMs
      ofMillis clamped

def plus? (a b : Duration) : Option Duration :=
  if a.isInNanos == b.isInNanos then
    if a.isInNanos then
      some (ofNanosNormalized (a.rawUnits + b.rawUnits))
    else
      let m1 := a.rawUnits
      let m2 := b.rawUnits
      if m1 == maxMillis || m1 == -maxMillis then
        if (m2 != maxMillis && m2 != -maxMillis) ||
            ((m1.toUInt64 ^^^ m2.toUInt64).toBitVec.slt 0#64 == false) then
          some a
        else
          none
      else if m2 == maxMillis || m2 == -maxMillis then
        some b
      else
        let sum := m1.toInt + m2.toInt
        if sum >= 4611686018427387903 then some (ofMillis maxMillis)
        else if sum <= -4611686018427387903 then some (ofMillis (-maxMillis))
        else some (ofMillisNormalized (Int64.ofInt sum))
  else if !a.isInNanos then
    some (addMixed b.rawUnits a.rawUnits)
  else
    some (addMixed a.rawUnits b.rawUnits)

def plus (a b : Duration) : Duration :=
  (plus? a b).getD zero

end Duration

/-- Model of `DateTimePeriod.totalNanoseconds`. -/
def totalNanosecondsModel (p : DateTimePeriodModel) : Int64 :=
  Int64.ofInt p.nanoseconds.toInt +
    (Duration.ofIntUnit p.seconds .seconds).inWholeNanoseconds +
    (Duration.ofIntUnit p.minutes .minutes).inWholeNanoseconds +
    (Duration.ofIntUnit p.hours .hours).inWholeNanoseconds

/-- Model of `DateTimePeriod.dateComponentInWholeUnits` (`none` traps on zero divisor). -/
def dateComponentInWholeUnitsModel (p : DateTimePeriodModel) : DateBasedUnit → Option Int32
  | .dayBased d => if d == 0 then none else some (jvmI32Div p.days d)
  | .monthBased m => if m == 0 then none else some (jvmI32Div p.months m)

/-- Model of `DateTimePeriod.timeComponentInWholeUnits` (`none` traps on zero divisor). -/
def timeComponentInWholeUnitsModel (p : DateTimePeriodModel) (u : TimeBasedUnit) : Option Int64 :=
  if u.nanoseconds == 0 then none
  else some (jvmI64Div (totalNanosecondsModel p) u.nanoseconds)

/-- Model of `DateTimePeriod.timeComponentDuration`. -/
def timeComponentDurationModel (p : DateTimePeriodModel) : Duration :=
  Duration.ofLongUnit (totalNanosecondsModel p) .nanoseconds

/-- Model of `DateTimePeriod.dateComponentApproximateDuration`. -/
def dateComponentApproximateDurationModel (p : DateTimePeriodModel) : Duration :=
  let daysDur := Duration.ofIntUnit p.days .days
  let monthsYearsDays : Float := (p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422
  let monthsYearsDur := Duration.ofDaysFloat monthsYearsDays
  let combined := Duration.plus daysDur monthsYearsDur
  Duration.ofLongUnit combined.inWholeNanoseconds .nanoseconds

/-- Model of `DateTimePeriod.approximateDuration`. -/
def approximateDurationModel (p : DateTimePeriodModel) : Duration :=
  Duration.plus (timeComponentDurationModel p) (dateComponentApproximateDurationModel p)

/-- Model of `DateTimePeriod.approximateDurationInMinutes`. -/
def approximateDurationInMinutesModel (p : DateTimePeriodModel) : Float :=
  let totalNs := (approximateDurationModel p).inWholeNanoseconds
  let oneMinuteNs := (Duration.ofIntUnit 1 .minutes).inWholeNanoseconds
  Jvm.i64ToFloat totalNs.toUInt64 / Jvm.i64ToFloat oneMinuteNs.toUInt64

/-- Standalone model of `Instant.periodUntilWithUnit(other, unit, timeZone)` given `untilVal = until(other, unit, timeZone)`. -/
def periodUntilWithUnitModel (untilVal : Int64) (unit : DateTimeUnit) : DateTimePeriodModel :=
  match unit with
  | .timeBased u =>
    DateTimePeriodModel.ofNanoseconds (u.nanoseconds * untilVal)
  | .dateBased (.dayBased d) =>
    DateTimePeriodModel.ofDays (Int32.ofInt (Int64.ofInt d.toInt * untilVal).toInt)
  | .dateBased (.monthBased m) =>
    DateTimePeriodModel.ofMonths (Int32.ofInt (Int64.ofInt m.toInt * untilVal).toInt)

/-- Standalone model of `Instant.periodUntilWithUnit(other, unit)` for `TimeBased` units. -/
def periodUntilWithUnitTimeModel (untilVal : Int64) (unit : TimeBasedUnit) : DateTimePeriodModel :=
  DateTimePeriodModel.ofNanoseconds (unit.nanoseconds * untilVal)

/-- Standalone model of `Instant.periodUntilWithProgressiveUnits` over a list of `(unit, period)` pairs. -/
def periodUntilWithProgressiveUnitsModel
    (periods : List (DateTimeUnit × DateTimePeriodModel)) :
    Option (DateTimeUnit × DateTimePeriodModel) :=
  let chosen := periods.find? fun (u, p) =>
    match u with
    | .timeBased tu =>
      match timeComponentInWholeUnitsModel p tu with
      | some v => v != 0
      | none => false
    | .dateBased du =>
      match dateComponentInWholeUnitsModel p du with
      | some v => v != 0
      | none => false
  match chosen with
  | some pair => some pair
  | none => periods.getLast?

/-- Standalone model of `Instant.periodUntilWithProgressiveUnits` for `TimeBased` units. -/
def periodUntilWithProgressiveUnitsTimeModel
    (periods : List (TimeBasedUnit × DateTimePeriodModel)) :
    Option (TimeBasedUnit × DateTimePeriodModel) :=
  let chosen := periods.find? fun (u, p) =>
    match timeComponentInWholeUnitsModel p u with
    | some v => v != 0
    | none => false
  match chosen with
  | some pair => some pair
  | none => periods.getLast?

end TimeUtil.Model

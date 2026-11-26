/*
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
 */

package com.alexvanyo.composelife.timeutil

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `PeriodUntil.kt` by lifting the actual compiled
 * `PeriodUntilKt.class` JVM bytecode from the test runtime classpath into Lean 4 and proving theorems about that
 * real bytecode with `lake env lean`.
 */
class PeriodUntilVerificationTests {
    @Test
    fun getTotalNanoseconds_bytecode_computes_exact_total() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_getTotalNanoseconds_exact_total",
            leanBody = """
                |theorem real_getTotalNanoseconds_exact_total
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
                |    (hd : 1 ≤ d) (hf : 40 ≤ fuel)
                |    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
                |    (hc : HasTimeStaticsClean jh) :
                |    ∃ n : Int64,
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_getTotalNanoseconds_prog
                |            (initTimeJvmState [(0, .ext (.period p))] hp jh) =
                |          some (.i64 n.toUInt64, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      n = totalNanosecondsModel p ∧
                |      ((-(76861433 : Int) ≤ p.minutes.toInt ∧ p.minutes.toInt ≤ 76861433) →
                |        (-(1281023 : Int) ≤ p.hours.toInt ∧ p.hours.toInt ≤ 1281023) →
                |        (-(2 ^ 63 : Int) ≤ p.nanoseconds.toInt +
                |            1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) ∧
                |          p.nanoseconds.toInt +
                |            1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt) <
                |              (2 ^ 63 : Int)) →
                |        n.toInt = p.nanoseconds.toInt +
                |          1000000000 * (p.seconds.toInt + 60 * p.minutes.toInt + 3600 * p.hours.toInt)) := by
                |  have hprog : TimeUtil.RealJvmBytecode.PeriodUntilKt_getTotalNanoseconds_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_getTotalNanoseconds_prog := rfl
                |  rw [hprog]
                |  exact ⟨_, getTotalNanoseconds_equiv resolveProg d subFuel fuel hd hf p hp jh hc, rfl,
                |    fun hm hh hs => totalNanosecondsModel_exact_bounded p hm hh hs⟩
            """.trimMargin(),
        )
    }

    @Test
    fun componentInWholeUnits_bytecode_truncates_and_traps_on_zero_unit() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_componentInWholeUnits_truncate_and_trap",
            leanBody = """
                |theorem real_componentInWholeUnits_truncate_and_trap
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d subFuel fuel : Nat) (hd : 2 ≤ d) (hsf : 40 ≤ subFuel) (hf : 30 ≤ fuel)
                |    (p : DateTimePeriodModel) (days : Int32) (hdays : 0 < days.toInt)
                |    (u : TimeBasedUnit) (hu : 0 < u.nanoseconds.toInt)
                |    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh) :
                |    (∃ q : Int32,
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_dateComponentInWholeUnits_prog
                |            (initTimeJvmState [(0, .ext (.period p)),
                |              (1, .ext (.timeUnit (.dateBased (.dayBased days))))] hp jh) =
                |          some (.i32 q.toUInt32, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      (p.days.toInt - q.toInt * days.toInt).natAbs < days.toInt.natAbs ∧
                |      (0 ≤ p.days.toInt → 0 ≤ q.toInt ∧ 0 ≤ p.days.toInt - q.toInt * days.toInt) ∧
                |      (p.days.toInt ≤ 0 → q.toInt ≤ 0 ∧ p.days.toInt - q.toInt * days.toInt ≤ 0)) ∧
                |    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |        TimeUtil.RealJvmBytecode.PeriodUntilKt_dateComponentInWholeUnits_prog
                |        (initTimeJvmState [(0, .ext (.period p)),
                |          (1, .ext (.timeUnit (.dateBased (.dayBased 0))))] hp jh) = none ∧
                |    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |        TimeUtil.RealJvmBytecode.PeriodUntilKt_dateComponentInWholeUnits_prog
                |        (initTimeJvmState [(0, .ext (.period p)),
                |          (1, .ext (.timeUnit (.dateBased (.monthBased 0))))] hp jh) = none ∧
                |    (∃ q : Int64,
                |      (∃ endSt,
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_timeComponentInWholeUnits_prog
                |            (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.timeBased u)))] hp jh) =
                |          some (.i64 q.toUInt64, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |      ((totalNanosecondsModel p).toInt - q.toInt * u.nanoseconds.toInt).natAbs <
                |        u.nanoseconds.toInt.natAbs ∧
                |      (0 ≤ (totalNanosecondsModel p).toInt →
                |        0 ≤ q.toInt ∧ 0 ≤ (totalNanosecondsModel p).toInt - q.toInt * u.nanoseconds.toInt) ∧
                |      ((totalNanosecondsModel p).toInt ≤ 0 →
                |        q.toInt ≤ 0 ∧ (totalNanosecondsModel p).toInt - q.toInt * u.nanoseconds.toInt ≤ 0)) ∧
                |    Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |        TimeUtil.RealJvmBytecode.PeriodUntilKt_timeComponentInWholeUnits_prog
                |        (initTimeJvmState [(0, .ext (.period p)), (1, .ext (.timeUnit (.timeBased ⟨0⟩)))] hp jh) =
                |      none := by
                |  have hD : TimeUtil.RealJvmBytecode.PeriodUntilKt_dateComponentInWholeUnits_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_dateComponentInWholeUnits_prog := rfl
                |  have hT : TimeUtil.RealJvmBytecode.PeriodUntilKt_timeComponentInWholeUnits_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_timeComponentInWholeUnits_prog := rfl
                |  rw [hD, hT]
                |  obtain ⟨q, hq, -, hq2, hq3, hq4, -⟩ :=
                |    dateComponentInWholeUnitsModel_dayBased_truncation p days hdays
                |  obtain ⟨tq, htq, -, ht2, ht3, ht4, -⟩ := timeComponentInWholeUnitsModel_truncation p u hu
                |  obtain ⟨hz1, hz2⟩ := dateComponentInWholeUnitsModel_trap_zero p
                |  exact ⟨⟨q, dateComponentInWholeUnits_equiv resolveProg d subFuel fuel (by omega) (by omega)
                |      p _ q hq hp jh, hq2, hq3, hq4⟩,
                |    dateComponentInWholeUnits_divZero_traps resolveProg d subFuel fuel (by omega) (by omega)
                |      p _ hz1 hp jh,
                |    dateComponentInWholeUnits_divZero_traps resolveProg d subFuel fuel (by omega) (by omega)
                |      p _ hz2 hp jh,
                |    ⟨tq, timeComponentInWholeUnits_equiv resolveProg hext d subFuel fuel hd hsf (by omega)
                |      p u tq htq hp jh hc, ht2, ht3, ht4⟩,
                |    timeComponentInWholeUnits_divZero_traps resolveProg hext d subFuel fuel hd hsf (by omega)
                |      p ⟨0⟩ (timeComponentInWholeUnitsModel_trap_zero p) hp jh hc⟩
            """.trimMargin(),
        )
    }

    @Test
    fun duration_getters_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_duration_getters_implement_model",
            leanBody = """
                |theorem real_duration_getters_implement_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d subFuel fuel : Nat) (hd : 4 ≤ d) (hsf : 40 ≤ subFuel) (hf : 40 ≤ fuel)
                |    (p : DateTimePeriodModel) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt)
                |    (hc : HasTimeStaticsClean jh)
                |    (hNotNaN :
                |      (Duration.ofDaysFloat? ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422)).isSome = true)
                |    (hPlusOk : (Duration.plus? (Duration.ofIntUnit p.days .days)
                |      (Duration.ofDaysFloat ((p.months.toFloat / 12.0 + p.years.toFloat) * 365.2422))).isSome = true)
                |    (hApproxOk : (Duration.plus? (timeComponentDurationModel p)
                |      (dateComponentApproximateDurationModel p)).isSome = true) :
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_getTimeComponentDuration_prog
                |          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
                |        some (.i64 (timeComponentDurationModel p).rawValue.toUInt64, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_getDateComponentApproximateDuration_prog
                |          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
                |        some (.i64 (dateComponentApproximateDurationModel p).rawValue.toUInt64, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_getApproximateDuration_prog
                |          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
                |        some (.i64 (approximateDurationModel p).rawValue.toUInt64, endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_getApproximateDurationInMinutes_prog
                |          (initTimeJvmState [(0, .ext (.period p))] hp jh) =
                |        some (.f64 (Jvm.i64ToFloat (approximateDurationModel p).inWholeNanoseconds.toUInt64 /
                |          60000000000.0), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have hT : TimeUtil.RealJvmBytecode.PeriodUntilKt_getTimeComponentDuration_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_getTimeComponentDuration_prog := rfl
                |  have hD : TimeUtil.RealJvmBytecode.PeriodUntilKt_getDateComponentApproximateDuration_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_getDateComponentApproximateDuration_prog := rfl
                |  have hA : TimeUtil.RealJvmBytecode.PeriodUntilKt_getApproximateDuration_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_getApproximateDuration_prog := rfl
                |  have hM : TimeUtil.RealJvmBytecode.PeriodUntilKt_getApproximateDurationInMinutes_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_getApproximateDurationInMinutes_prog := rfl
                |  rw [hT, hD, hA, hM, ← approximateDurationInMinutesModel_formula]
                |  exact ⟨getTimeComponentDuration_equiv resolveProg hext d subFuel fuel (by omega) hsf (by omega)
                |      p hp jh hc,
                |    getDateComponentApproximateDuration_equiv resolveProg d subFuel fuel (by omega) hf
                |      p hp jh hc hNotNaN hPlusOk,
                |    getApproximateDuration_equiv resolveProg hext d subFuel fuel (by omega) hsf (by omega)
                |      p hp jh hc hNotNaN hPlusOk hApproxOk,
                |    getApproximateDurationInMinutes_equiv resolveProg hext d subFuel fuel hd hsf (by omega)
                |      p hp jh hc hNotNaN hPlusOk hApproxOk⟩
            """.trimMargin(),
        )
    }

    @Test
    fun periodUntilWithUnit_bytecode_implements_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_periodUntilWithUnit_implements_model",
            leanBody = """
                |theorem real_periodUntilWithUnit_implements_model
                |    (resolveProg : String → Option (List JvmInstr)) (d subFuel fuel : Nat)
                |    (hd : 1 ≤ d) (hf : 50 ≤ fuel)
                |    (start other : Int64) (u : DateTimeUnit) (tu : TimeBasedUnit) (tz : String)
                |    (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) :
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog
                |          (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                |            (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz))] hp jh) =
                |        some (.ext (.period (periodUntilWithUnitModel (hp.untilTz start other u tz) u)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) fuel
                |          TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_1_prog
                |          (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                |            (2, .ext (.timeUnit (.timeBased tu)))] hp jh) =
                |        some (.ext (.period (periodUntilWithUnitTimeModel (hp.untilTime start other tu) tu)), endSt) ∧
                |      endSt.jvmHeap = jh ∧ endSt.heap = hp) := by
                |  have hU : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog := rfl
                |  have hU1 : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_1_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntilWithUnit_1_prog := rfl
                |  rw [hU, hU1]
                |  exact ⟨periodUntilWithUnit_equiv resolveProg d subFuel fuel hd hf start other u tz hp jh,
                |    periodUntilWithUnit_1_equiv resolveProg d subFuel fuel hd (by omega) start other tu hp jh⟩
            """.trimMargin(),
        )
    }

    @Test
    fun periodUntilWithProgressiveUnits_bytecode_implements_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_periodUntilWithProgressiveUnits_implements_model",
            leanBody = """
                |theorem real_periodUntilWithProgressiveUnits_implements_model
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d subFuel : Nat) (hd : 3 ≤ d) (hsf : 50 ≤ subFuel)
                |    (start other : Int64) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
                |    (listAddr arrAddr : Nat)
                |    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)])) :
                |    (∀ (units : List DateTimeUnit) (tz : String),
                |      units ≠ [] → units.length < 2 ^ 31 →
                |      (∀ u ∈ units, periodNoAbsMin (periodUntilWithUnitModel (hp.untilTz start other u tz) u) u) →
                |      jh.get? arrAddr = some (.objArray "kotlinx/datetime/DateTimeUnit"
                |        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) →
                |      ∃ resPair endSt,
                |        periodUntilWithProgressiveUnitsModel
                |          (units.map fun u => (u, periodUntilWithUnitModel (hp.untilTz start other u tz) u)) =
                |            some resPair ∧
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (70 * units.length + 70)
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_prog
                |            (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                |              (2, .heapRef listAddr), (3, .ext (.timeZone tz))] hp jh) =
                |          some (unitPairVal resPair.1 resPair.2, endSt) ∧
                |        HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp) ∧
                |    (∀ units : List TimeBasedUnit,
                |      units ≠ [] → units.length < 2 ^ 31 →
                |      (∀ u ∈ units,
                |        timePeriodNoAbsMin (periodUntilWithUnitTimeModel (hp.untilTime start other u) u) u) →
                |      jh.get? arrAddr = some (.objArray "kotlinx/datetime/DateTimeUnit${'$'}TimeBased"
                |        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) →
                |      ∃ resPair endSt,
                |        periodUntilWithProgressiveUnitsTimeModel
                |          (units.map fun u => (u, periodUntilWithUnitTimeModel (hp.untilTime start other u) u)) =
                |            some resPair ∧
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) (70 * units.length + 70)
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog
                |            (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.instant other)),
                |              (2, .heapRef listAddr)] hp jh) =
                |          some (unitTimePairVal resPair.1 resPair.2, endSt) ∧
                |        HasTimeStaticsClean endSt.jvmHeap ∧ endSt.heap = hp) := by
                |  have hP : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_prog := rfl
                |  have hP1 : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog := rfl
                |  rw [hP, hP1]
                |  exact ⟨fun units tz hne hlen hNotMin harr =>
                |      periodUntilWithProgressiveUnits_equiv resolveProg hext d subFuel _ hd hsf start other units tz
                |        hne hlen (Nat.le_refl _) hp hNotMin listAddr arrAddr jh hc hlist harr,
                |    fun units hne hlen hNotMin harr =>
                |      periodUntilWithProgressiveUnits_1_equiv resolveProg hext d subFuel _ hd hsf start other units
                |        hne hlen (Nat.le_refl _) hp hNotMin listAddr arrAddr jh hc hlist harr⟩
            """.trimMargin(),
        )
    }

    @Test
    fun periodUntil_composables_bytecode_initial_composition() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_periodUntil_composables_initial_composition",
            leanBody = """
                |theorem real_periodUntil_composables_initial_composition
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d subFuel : Nat) (hd : 2 ≤ d) (hsf : 50 ≤ subFuel)
                |    (start : Int64) (clockId : Nat) (u : DateTimeUnit) (tu : TimeBasedUnit) (tz : String)
                |    (changed : UInt32) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
                |    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) 200 TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_prog
                |        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
                |          (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz)), (4, .ext .composer), (5, .i32 changed)]
                |          hp jh) =
                |        some (.ext (.period (periodUntilWithUnitModel
                |          (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u)), endSt) ∧
                |      endSt.jvmHeap = jh ∧
                |      endSt.heap.clockReads = hp.clockReads + 1 ∧
                |      endSt.heap.closures = hp.closures.push ("PeriodUntilKt${'$'}periodUntil${'$'}2${'$'}1",
                |        [.ext (.timeUnit u), .ext (.instant start), .ext (.timeZone tz), .ext (.clock clockId)]) ∧
                |      endSt.heap.composer.stateCells = (hp.composer.nextStateId, .ext (.period
                |          (periodUntilWithUnitModel (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u))) ::
                |        hp.composer.stateCells ∧
                |      endSt.heap.composer.groupStack = []) ∧
                |    (∃ endSt,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) 200 TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_1_prog
                |        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
                |          (2, .ext (.timeUnit (.timeBased tu))), (3, .ext .composer), (4, .i32 changed)] hp jh) =
                |        some (.ext (.period (periodUntilWithUnitTimeModel
                |          (hp.untilTime start (hp.clockNow hp.clockReads) tu) tu)), endSt) ∧
                |      endSt.jvmHeap = jh ∧
                |      endSt.heap.clockReads = hp.clockReads + 1 ∧
                |      endSt.heap.closures = hp.closures.push ("PeriodUntilKt${'$'}periodUntil${'$'}4${'$'}1",
                |        [.ext (.instant start), .ext (.timeUnit (.timeBased tu)), .ext (.clock clockId)]) ∧
                |      endSt.heap.composer.stateCells = (hp.composer.nextStateId, .ext (.period
                |          (periodUntilWithUnitTimeModel (hp.untilTime start (hp.clockNow hp.clockReads) tu) tu))) ::
                |        hp.composer.stateCells ∧
                |      endSt.heap.composer.groupStack = []) := by
                |  have hC : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_prog = TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntil_prog :=
                |    rfl
                |  have hC1 : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_1_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntil_1_prog := rfl
                |  rw [hC, hC1]
                |  exact ⟨periodUntil_initialComposition_equiv resolveProg hext d subFuel 200 hd hsf (Nat.le_refl _)
                |      start clockId u tz changed hp jh hc hgroups hstack,
                |    periodUntil_1_initialComposition_equiv resolveProg hext d subFuel 200 hd (by omega)
                |      (Nat.le_refl _) start clockId tu changed hp jh hc hgroups hstack⟩
            """.trimMargin(),
        )
    }

    @Test
    fun periodUntil_composable_bytecode_matches_helper_bytecode_on_clock_reading() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_periodUntil_composable_matches_helper",
            leanBody = """
                |theorem real_periodUntil_composable_matches_helper
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d subFuel : Nat) (hd : 2 ≤ d) (hsf : 50 ≤ subFuel)
                |    (start : Int64) (clockId : Nat) (u : DateTimeUnit) (tz : String)
                |    (changed : UInt32) (hp : TimeHeap) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
                |    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
                |    ∃ v e1 e2,
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) 200 TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_prog
                |        (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
                |          (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz)), (4, .ext .composer), (5, .i32 changed)]
                |          hp jh) = some (v, e1) ∧
                |      Jvm.runJvmRes (mkTimeHooks resolveProg d subFuel) 50
                |        TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog
                |        (initTimeJvmState [(0, .ext (.instant start)),
                |          (1, .ext (.instant (hp.clockNow hp.clockReads))),
                |          (2, .ext (.timeUnit u)), (3, .ext (.timeZone tz))] hp jh) = some (v, e2) ∧
                |      e1.heap.clockReads = hp.clockReads + 1 := by
                |  have hC : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntil_prog = TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntil_prog :=
                |    rfl
                |  have hU : TimeUtil.RealJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_periodUntilWithUnit_prog := rfl
                |  rw [hC, hU]
                |  obtain ⟨e1, h1, -, hreads, -⟩ := periodUntil_initialComposition_equiv resolveProg hext d subFuel 200
                |    hd hsf (Nat.le_refl _) start clockId u tz changed hp jh hc hgroups hstack
                |  obtain ⟨e2, h2, -⟩ := periodUntilWithUnit_equiv resolveProg d subFuel 50 (by omega) (Nat.le_refl _)
                |    start (hp.clockNow hp.clockReads) u tz hp jh
                |  exact ⟨_, e1, e2, h1, h2, hreads⟩
            """.trimMargin(),
        )
    }

    @Test
    fun progressivePeriodUntil_composables_bytecode_initial_composition() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_progressivePeriodUntil_composables_initial_composition",
            leanBody = """
                |theorem real_progressivePeriodUntil_composables_initial_composition
                |    (resolveProg : String → Option (List JvmInstr)) (hext : ExtendsTimeProgs resolveProg)
                |    (d : Nat) (hd : 4 ≤ d) (clockId : Nat) (start : Int64) (changed : UInt32)
                |    (hp : TimeHeap) (listAddr arrAddr : Nat) (jh : Jvm.JvmHeap TimeExt) (hc : HasTimeStaticsClean jh)
                |    (hlist : jh.get? listAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef arrAddr)]))
                |    (hgroups : hp.composer.groups = []) (hstack : hp.composer.groupStack = []) :
                |    (∀ (units : List DateTimeUnit) (tz : String),
                |      units ≠ [] → units.length < 2 ^ 31 →
                |      (∀ u ∈ units, periodNoAbsMin
                |        (periodUntilWithUnitModel (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u) u) →
                |      jh.get? arrAddr = some (.objArray "kotlinx/datetime/DateTimeUnit"
                |        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit u)).toArray) →
                |      ∃ resPair endSt,
                |        periodUntilWithProgressiveUnitsModel (units.map fun u =>
                |          (u, periodUntilWithUnitModel (hp.untilTz start (hp.clockNow hp.clockReads) u tz) u)) =
                |            some resPair ∧
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d (70 * units.length + 70)) 220
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_progressivePeriodUntil_prog
                |            (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
                |              (2, .heapRef listAddr), (3, .ext (.timeZone tz)), (4, .ext .composer),
                |              (5, .i32 changed)] hp jh) =
                |          some (unitPairVal resPair.1 resPair.2, endSt) ∧
                |        HasTimeStaticsClean endSt.jvmHeap ∧
                |        endSt.heap.clockReads = hp.clockReads + 1 ∧
                |        endSt.heap.closures = hp.closures.push
                |          ("PeriodUntilKt${'$'}progressivePeriodUntil${'$'}2${'$'}1",
                |            [.heapRef listAddr, .ext (.clock clockId), .ext (.instant start), .ext (.timeZone tz)]) ∧
                |        endSt.heap.composer.stateCells =
                |          (hp.composer.nextStateId, unitPairVal resPair.1 resPair.2) :: hp.composer.stateCells ∧
                |        endSt.heap.composer.groupStack = []) ∧
                |    (∀ units : List TimeBasedUnit,
                |      units ≠ [] → units.length < 2 ^ 31 →
                |      (∀ u ∈ units, timePeriodNoAbsMin
                |        (periodUntilWithUnitTimeModel (hp.untilTime start (hp.clockNow hp.clockReads) u) u) u) →
                |      jh.get? arrAddr = some (.objArray "kotlinx/datetime/DateTimeUnit${'$'}TimeBased"
                |        (units.map fun u => Jvm.JvmVal.ext (TimeExt.timeUnit (.timeBased u))).toArray) →
                |      ∃ resPair endSt,
                |        periodUntilWithProgressiveUnitsTimeModel (units.map fun u =>
                |          (u, periodUntilWithUnitTimeModel (hp.untilTime start (hp.clockNow hp.clockReads) u) u)) =
                |            some resPair ∧
                |        Jvm.runJvmRes (mkTimeHooks resolveProg d (70 * units.length + 70)) 220
                |            TimeUtil.RealJvmBytecode.PeriodUntilKt_progressivePeriodUntil_1_prog
                |            (initTimeJvmState [(0, .ext (.instant start)), (1, .ext (.clock clockId)),
                |              (2, .heapRef listAddr), (3, .ext .composer), (4, .i32 changed)] hp jh) =
                |          some (unitTimePairVal resPair.1 resPair.2, endSt) ∧
                |        HasTimeStaticsClean endSt.jvmHeap ∧
                |        endSt.heap.clockReads = hp.clockReads + 1 ∧
                |        endSt.heap.closures = hp.closures.push
                |          ("PeriodUntilKt${'$'}progressivePeriodUntil${'$'}4${'$'}1",
                |            [.heapRef listAddr, .ext (.clock clockId), .ext (.instant start)]) ∧
                |        endSt.heap.composer.stateCells =
                |          (hp.composer.nextStateId, unitTimePairVal resPair.1 resPair.2) :: hp.composer.stateCells ∧
                |        endSt.heap.composer.groupStack = []) := by
                |  have hP : TimeUtil.RealJvmBytecode.PeriodUntilKt_progressivePeriodUntil_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_progressivePeriodUntil_prog := rfl
                |  have hP1 : TimeUtil.RealJvmBytecode.PeriodUntilKt_progressivePeriodUntil_1_prog =
                |      TimeUtil.KotlinJvmBytecode.PeriodUntilKt_progressivePeriodUntil_1_prog := rfl
                |  rw [hP, hP1]
                |  exact ⟨fun units tz hne hlen hNotMin harr =>
                |      progressivePeriodUntil_initialComposition_equiv resolveProg hext d _ 220 hd (Nat.le_refl _)
                |        start clockId units tz changed hne hlen (Nat.le_refl _) hp hNotMin listAddr arrAddr jh hc
                |        hlist harr hgroups hstack,
                |    fun units hne hlen hNotMin harr =>
                |      progressivePeriodUntil_1_initialComposition_equiv resolveProg hext d _ 220 hd (Nat.le_refl _)
                |        start clockId units changed hne hlen (Nat.le_refl _) hp hNotMin listAddr arrAddr jh hc
                |        hlist harr hgroups hstack⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "time-util",
            classResourcePath = "com/alexvanyo/composelife/timeutil/PeriodUntilKt.class",
            realBytecodeNamespace = "TimeUtil.RealJvmBytecode",
            instrType = "TimeUtil.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "PeriodUntilKt_periodUntil_prog",
                "PeriodUntilKt_periodUntil_1_prog",
                "PeriodUntilKt_progressivePeriodUntil_prog",
                "PeriodUntilKt_progressivePeriodUntil_1_prog",
                "PeriodUntilKt_periodUntilWithUnit_prog",
                "PeriodUntilKt_periodUntilWithUnit_1_prog",
                "PeriodUntilKt_periodUntilWithProgressiveUnits_prog",
                "PeriodUntilKt_periodUntilWithProgressiveUnits_1_prog",
                "PeriodUntilKt_dateComponentInWholeUnits_prog",
                "PeriodUntilKt_timeComponentInWholeUnits_prog",
                "PeriodUntilKt_getTotalNanoseconds_prog",
                "PeriodUntilKt_getTimeComponentDuration_prog",
                "PeriodUntilKt_getDateComponentApproximateDuration_prog",
                "PeriodUntilKt_getApproximateDuration_prog",
                "PeriodUntilKt_getApproximateDurationInMinutes_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.PeriodUntilModel",
                "theorems.PeriodUntilModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.PeriodUntil",
                "proofs.KotlinJvmEquiv.PeriodUntilCompose",
            ),
            defaultOpens = listOf(
                "TimeUtil",
                "TimeUtil.JvmVerification",
                "TimeUtil.Model",
                "TimeUtil.KotlinJvmVerification",
            ),
        )
    }
}

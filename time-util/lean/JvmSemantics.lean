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

import Jvm
import models.PeriodUntilModel

namespace TimeUtil.JvmVerification

export Jvm (JvmInstr setLocal initJvmState)

/-- Time-util + Compose domain-specific extension values on the JVM stack and locals. -/
inductive TimeExt where
  | period (p : Model.DateTimePeriodModel)
  | timeUnit (u : Model.DateTimeUnit)
  | instant (epochNs : Int64)
  | timeZone (tzId : String)
  | clock (id : Nat)
  | durationUnit (u : Model.DurationUnit)
  | composerEmpty
  | composer
  | composerKey (parts : List String)
  | stateRef (stateId : Nat)
  | closureRef (closureId : Nat)
  | companion (cls : String)
  | unit
  deriving DecidableEq, Repr, Inhabited

abbrev JvmVal := Jvm.JvmVal TimeExt

/-! ### Lightweight Compose Slot-Table Model for Movable Groups & Remember -/

namespace Compose

structure GroupEntry (Val : Type) where
  key : Int32
  slots : List Val := []
  deriving Repr, Inhabited

structure ActiveGroupFrame where
  key : Int32
  cursor : Nat := 0
  lastReadIdx? : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

structure ComposerModel (Val : Type) where
  inserting : Bool := true
  groups : List (GroupEntry Val) := []
  groupStack : List ActiveGroupFrame := []
  stateCells : List (Nat × Val) := []
  nextStateId : Nat := 0
  traceEnabled : Bool := false
  deriving Repr, Inhabited

def listSetAt {α : Type} : List α → Nat → α → List α
  | [], 0, v => [v]
  | [], n + 1, v => v :: listSetAt [] n v
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSetAt xs n v

def upsertGroup {Val : Type} (k : Int32) : List (GroupEntry Val) → List (GroupEntry Val)
  | [] => [{ key := k }]
  | g :: gs => if g.key == k then g :: gs else g :: upsertGroup k gs

def updateGroup {Val : Type} (k : Int32) (f : GroupEntry Val → GroupEntry Val) :
    List (GroupEntry Val) → List (GroupEntry Val)
  | [] => []
  | g :: gs => if g.key == k then f g :: gs else g :: updateGroup k f gs

def findGroup? {Val : Type} (k : Int32) : List (GroupEntry Val) → Option (GroupEntry Val)
  | [] => none
  | g :: gs => if g.key == k then some g else findGroup? k gs

def startMovableGroup {Val : Type} (m : ComposerModel Val) (key : Int32) : ComposerModel Val :=
  let groups' := upsertGroup key m.groups
  let frame : ActiveGroupFrame := { key := key, cursor := 0 }
  { m with groups := groups', groupStack := frame :: m.groupStack }

def endMovableGroup {Val : Type} (m : ComposerModel Val) : ComposerModel Val :=
  match m.groupStack with
  | _ :: rest => { m with groupStack := rest }
  | [] => m

def checkChangedSlot {Val : Type} [Inhabited Val] (beqVal : Val → Val → Bool)
    (m : ComposerModel Val) (newVal : Val) : Bool × ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match findGroup? f.key m.groups with
    | some g =>
      match g.slots[f.cursor]? with
      | some oldVal =>
        let changed := !(beqVal oldVal newVal)
        let slots' := listSetAt g.slots f.cursor newVal
        let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
        (changed, { m with groups := groups', groupStack := { f with cursor := f.cursor + 1 } :: rest })
      | none =>
        let slots' := g.slots ++ [newVal]
        let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
        (true, { m with groups := groups', groupStack := { f with cursor := f.cursor + 1 } :: rest })
    | none => (true, m)
  | [] => (true, m)

def readRememberSlot {Val : Type} (m : ComposerModel Val) : Option Val × ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match findGroup? f.key m.groups with
    | some g =>
      let idx := f.cursor
      let val? := g.slots[idx]?
      (val?, { m with groupStack := { f with cursor := idx + 1, lastReadIdx? := some idx } :: rest })
    | none => (none, m)
  | [] => (none, m)

def writeRememberSlot {Val : Type} (m : ComposerModel Val) (val : Val) : ComposerModel Val :=
  match m.groupStack with
  | f :: rest =>
    match f.lastReadIdx?, findGroup? f.key m.groups with
    | some idx, some g =>
      let slots' :=
        if idx < g.slots.length then listSetAt g.slots idx val
        else g.slots ++ [val]
      let groups' := updateGroup f.key (fun g0 => { g0 with slots := slots' }) m.groups
      { m with groups := groups', groupStack := { f with lastReadIdx? := none } :: rest }
    | _, _ => m
  | [] => m

def allocState {Val : Type} (m : ComposerModel Val) (initial : Val) : Nat × ComposerModel Val :=
  let sid := m.nextStateId
  (sid, { m with stateCells := (sid, initial) :: m.stateCells, nextStateId := sid + 1 })

def readState {Val : Type} (m : ComposerModel Val) (sid : Nat) : Option Val :=
  (m.stateCells.find? (fun (id, _) => id == sid)).map Prod.snd

end Compose

/-- Default UTC `Instant.until` oracle for `TimeBased` units. -/
def defaultUntilTime (start other : Int64) (u : Model.TimeBasedUnit) : Int64 :=
  if u.nanoseconds == 0 then 0
  else Model.jvmI64Div (other - start) u.nanoseconds

/-- Default UTC `Instant.until` oracle for general `DateTimeUnit`. -/
def defaultUntilTz (start other : Int64) (u : Model.DateTimeUnit) (_tz : String) : Int64 :=
  match u with
  | .timeBased tb => defaultUntilTime start other tb
  | .dateBased (.dayBased d) =>
    if d == 0 then 0
    else Model.jvmI64Div (other - start) (Int64.ofInt (d.toInt * 86400000000000))
  | .dateBased (.monthBased _) => 0

/-- Combined Compose slot-table + closure table + clock/until oracle heap state. -/
structure TimeHeap where
  composer : Compose.ComposerModel JvmVal := {}
  closures : Array (String × List JvmVal) := #[]
  clockReads : Nat := 0
  clockNow : Nat → Int64 := fun _ => 0
  untilTz : Int64 → Int64 → Model.DateTimeUnit → String → Int64 := defaultUntilTz
  untilTime : Int64 → Int64 → Model.TimeBasedUnit → Int64 := defaultUntilTime
  deriving Inhabited

abbrev JvmState := Jvm.JvmState TimeExt TimeHeap

/-- Strip the timeutil package prefix consistently for kernel reduction. -/
def normalizeTimeClass : String → String
  | "com/alexvanyo/composelife/timeutil/PeriodUntilKt" => "PeriodUntilKt"
  | "com/alexvanyo/composelife/timeutil/PeriodUntilKt$periodUntil$2$1" => "PeriodUntilKt$periodUntil$2$1"
  | "com/alexvanyo/composelife/timeutil/PeriodUntilKt$periodUntil$4$1" => "PeriodUntilKt$periodUntil$4$1"
  | "com/alexvanyo/composelife/timeutil/PeriodUntilKt$progressivePeriodUntil$2$1" =>
    "PeriodUntilKt$progressivePeriodUntil$2$1"
  | "com/alexvanyo/composelife/timeutil/PeriodUntilKt$progressivePeriodUntil$4$1" =>
    "PeriodUntilKt$progressivePeriodUntil$4$1"
  | cls => cls

/-- Structural equality on `TimeExt` values used by `Intrinsics.areEqual` and Compose slots. -/
def beqTimeExt : TimeExt → TimeExt → Bool :=
  fun a b => decide (a = b)

/-- Reference identity on `TimeExt` used by `if_acmpeq` / `if_acmpne`. -/
def beqRefTimeExt : TimeExt → TimeExt → Option Bool
  | .composerEmpty, .composerEmpty => some true
  | .composerEmpty, .period _ => some false
  | .period _, .composerEmpty => some false
  | .composerEmpty, .timeUnit _ => some false
  | .timeUnit _, .composerEmpty => some false
  | .composerEmpty, .instant _ => some false
  | .instant _, .composerEmpty => some false
  | .composerEmpty, .timeZone _ => some false
  | .timeZone _, .composerEmpty => some false
  | .composerEmpty, .clock _ => some false
  | .clock _, .composerEmpty => some false
  | .composerEmpty, .stateRef _ => some false
  | .stateRef _, .composerEmpty => some false
  | .composerEmpty, .closureRef _ => some false
  | .closureRef _, .composerEmpty => some false
  | .composerEmpty, .composer => some false
  | .composer, .composerEmpty => some false
  | .stateRef a, .stateRef b => some (a == b)
  | .closureRef a, .closureRef b => some (a == b)
  | .composer, .composer => some true
  | .unit, .unit => some true
  | _, _ => none

/-- Initial JVM execution state for `time-util` verification. -/
def initTimeJvmState (slots : List (Nat × JvmVal))
    (heap : TimeHeap := {}) (jvmHeap : Jvm.JvmHeap TimeExt := {}) : JvmState :=
  Jvm.initJvmState slots (.i32 0) heap jvmHeap

/-- Allocate a closure `(fnTag, captures)` in `TimeHeap` and return `(closureId, updatedHeap)`. -/
def allocClosure (h : TimeHeap) (fnTag : String) (captures : List JvmVal) : Nat × TimeHeap :=
  let id := h.closures.size
  (id, { h with closures := h.closures.push (fnTag, captures) })

def assignParamLocalsAux (idx : Nat) : List Char → List JvmVal → List (Nat × JvmVal)
  | 'J' :: tags, v :: vs | 'D' :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 2) tags vs
  | _ :: tags, v :: vs => (idx, v) :: assignParamLocalsAux (idx + 1) tags vs
  | _, _ => []

private def resolveTimeStatic (_st : JvmState) (cls field _desc : String) : Option JvmVal :=
  match normalizeTimeClass cls, field with
  | "kotlin/time/Duration", "Companion" => some (.ext (.companion "kotlin/time/Duration$Companion"))
  | "kotlin/time/DurationUnit", "NANOSECONDS" => some (.ext (.durationUnit .nanoseconds))
  | "kotlin/time/DurationUnit", "MICROSECONDS" => some (.ext (.durationUnit .microseconds))
  | "kotlin/time/DurationUnit", "MILLISECONDS" => some (.ext (.durationUnit .milliseconds))
  | "kotlin/time/DurationUnit", "SECONDS" => some (.ext (.durationUnit .seconds))
  | "kotlin/time/DurationUnit", "MINUTES" => some (.ext (.durationUnit .minutes))
  | "kotlin/time/DurationUnit", "HOURS" => some (.ext (.durationUnit .hours))
  | "kotlin/time/DurationUnit", "DAYS" => some (.ext (.durationUnit .days))
  | "androidx/compose/runtime/Composer", "Companion" =>
    some (.ext (.companion "androidx/compose/runtime/Composer$Companion"))
  | "kotlin/Unit", "INSTANCE" => some (.ext .unit)
  | _, _ => none

def checkTimeInstanceOf (cls : String) (v : JvmVal) : Bool :=
  match normalizeTimeClass cls, v with
  | "kotlinx/datetime/DateTimeUnit$TimeBased", .ext (.timeUnit (.timeBased _)) => true
  | "kotlinx/datetime/DateTimeUnit$DateBased", .ext (.timeUnit (.dateBased _)) => true
  | "kotlinx/datetime/DateTimeUnit$DayBased", .ext (.timeUnit (.dateBased (.dayBased _))) => true
  | "kotlinx/datetime/DateTimeUnit$MonthBased", .ext (.timeUnit (.dateBased (.monthBased _))) => true
  | "kotlinx/datetime/DateTimeUnit", .ext (.timeUnit _) => true
  | "kotlinx/datetime/DateTimePeriod", .ext (.period _) => true
  | "java/lang/Object", .ext _ => true
  | _, _ => false

def checkTimeCast (cls : String) (v : JvmVal) : Option JvmVal :=
  match normalizeTimeClass cls, v with
  | "kotlinx/datetime/DateTimeUnit$TimeBased", .ext (.timeUnit (.timeBased _)) => some v
  | "kotlinx/datetime/DateTimeUnit$DateBased", .ext (.timeUnit (.dateBased _)) => some v
  | "kotlinx/datetime/DateTimeUnit$DayBased", .ext (.timeUnit (.dateBased (.dayBased _))) => some v
  | "kotlinx/datetime/DateTimeUnit$MonthBased", .ext (.timeUnit (.dateBased (.monthBased _))) => some v
  | "kotlinx/datetime/DateTimeUnit", .ext (.timeUnit _) => some v
  | "kotlinx/datetime/DateTimePeriod", .ext (.period _) => some v
  | "androidx/compose/runtime/State", .ext (.stateRef _) => some v
  | "kotlin/jvm/functions/Function2", .ext (.closureRef _) => some v
  | "java/lang/Object", .ext _ => some v
  | _, _ => Jvm.defaultCheckCast (fun _ _ => none) cls v

def applyDateTimePeriodDefault (mask : UInt32) (yr mon day hr min sec : UInt32)
    (ns : UInt64) : Model.DateTimePeriodModel :=
  if mask == 63 then
    Model.DateTimePeriodModel.ofNanoseconds ns.toInt64
  else if mask == 123 then
    Model.DateTimePeriodModel.ofDays day.toInt32
  else if mask == 125 then
    Model.DateTimePeriodModel.ofMonths mon.toInt32
  else
    let y : Int := if (mask &&& 1) != 0 then 0 else yr.toInt32.toInt
    let mo : Int := if (mask &&& 2) != 0 then 0 else mon.toInt32.toInt
    let d : Int := if (mask &&& 4) != 0 then 0 else day.toInt32.toInt
    let h : Int := if (mask &&& 8) != 0 then 0 else hr.toInt32.toInt
    let mi : Int := if (mask &&& 16) != 0 then 0 else min.toInt32.toInt
    let s : Int := if (mask &&& 32) != 0 then 0 else sec.toInt32.toInt
    let n : Int := if (mask &&& 64) != 0 then 0 else ns.toInt64.toInt
    let totalMonths := y * 12 + mo
    let totalNs := n + 1000000000 * (s + 60 * mi + 3600 * h)
    {
      years := Int32.ofInt (totalMonths.tdiv 12)
      months := Int32.ofInt (totalMonths.tmod 12)
      days := Int32.ofInt d
      hours := Int32.ofInt (totalNs.tdiv 3600000000000)
      minutes := Int32.ofInt ((totalNs.tmod 3600000000000).tdiv 60000000000)
      seconds := Int32.ofInt ((totalNs.tmod 60000000000).tdiv 1000000000)
      nanoseconds := Int32.ofInt (totalNs.tmod 1000000000)
    }

def stepComposerInterface (st : JvmState) (method _desc : String) :
    Option JvmState ⊕ Option JvmVal :=
  match method, st.stack with
  | "joinKey", _b :: _a :: .ext .composer :: rest =>
    .inl (some { st with pc := st.pc + 1, stack := .ext (.composerKey []) :: rest })
  | "startMovableGroup", _dataKey :: keyVal :: .ext .composer :: rest =>
    match keyVal.asI32? with
    | some k =>
      let comp' := Compose.startMovableGroup st.heap.composer k.toInt32
      .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
    | none => .inr none
  | "endMovableGroup", .ext .composer :: rest =>
    let comp' := Compose.endMovableGroup st.heap.composer
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | "changedInstance", v :: .ext .composer :: rest =>
    let (changed, comp') := Compose.checkChangedSlot (Jvm.JvmVal.beqVal beqTimeExt) st.heap.composer v
    .inl (some { st with
      pc := st.pc + 1
      stack := .i32 (if changed then 1 else 0) :: rest
      heap := { st.heap with composer := comp' }
    })
  | "rememberedValue", .ext .composer :: rest =>
    let (v?, comp') := Compose.readRememberSlot st.heap.composer
    let outVal := v?.getD (.ext .composerEmpty)
    .inl (some { st with pc := st.pc + 1, stack := outVal :: rest, heap := { st.heap with composer := comp' } })
  | "updateRememberedValue", v :: .ext .composer :: rest =>
    let comp' := Compose.writeRememberSlot st.heap.composer v
    .inl (some { st with pc := st.pc + 1, stack := rest, heap := { st.heap with composer := comp' } })
  | _, _ => .inr none

/-- Hook builder parameterized by bytecode lookup (`resolveProg`) and bounded recursion depth/fuel. -/
def mkTimeHooks (resolveProg : String → Option (List JvmInstr)) (depth fuel : Nat) :
    Jvm.JvmHooks TimeExt TimeHeap :=
  match depth with
  | 0 => {
      beqExt := beqTimeExt
      beqRefExt := beqRefTimeExt
      checkInstanceOf := checkTimeInstanceOf
      checkCast := checkTimeCast
      resolveStatic := resolveTimeStatic
    }
  | d + 1 =>
    let invokeProg : JvmState → String → String → List JvmVal → Option (JvmVal × JvmState) :=
      fun st fnTag desc args =>
        match resolveProg fnTag with
        | some prog =>
          let hooks := mkTimeHooks resolveProg d fuel
          let tags := Jvm.parseMethodParamTags desc
          let subSt : JvmState := {
            pc := 0
            stack := []
            locals := (assignParamLocalsAux 0 tags args).foldl
              (fun loc (i, v) => setLocal loc i v) (fun _ => .i32 0)
            jvmHeap := st.jvmHeap
            heap := st.heap
          }
          match Jvm.runJvmRes hooks fuel prog subSt with
          | some (res, endSt) => some (res, { st with jvmHeap := endSt.jvmHeap, heap := endSt.heap })
          | none => none
        | none => none
    {
      beqExt := beqTimeExt
      beqRefExt := beqRefTimeExt
      checkInstanceOf := checkTimeInstanceOf
      checkCast := checkTimeCast
      resolveStatic := resolveTimeStatic
      stepInvokeSpecial := fun st cls method _desc =>
        match normalizeTimeClass cls, method, st.stack with
        | "PeriodUntilKt$periodUntil$2$1", "<init>",
            _cont :: clockV :: tzV :: thisV :: unitV :: .allocRef _ :: .allocRef _ :: rest =>
          let (cid, hp') := allocClosure st.heap "PeriodUntilKt$periodUntil$2$1" [unitV, thisV, tzV, clockV]
          .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := hp' })
        | "PeriodUntilKt$periodUntil$4$1", "<init>",
            _cont :: clockV :: unitV :: thisV :: .allocRef _ :: .allocRef _ :: rest =>
          let (cid, hp') := allocClosure st.heap "PeriodUntilKt$periodUntil$4$1" [thisV, unitV, clockV]
          .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := hp' })
        | "PeriodUntilKt$progressivePeriodUntil$2$1", "<init>",
            _cont :: tzV :: thisV :: clockV :: listV :: .allocRef _ :: .allocRef _ :: rest =>
          let (cid, hp') :=
            allocClosure st.heap "PeriodUntilKt$progressivePeriodUntil$2$1" [listV, clockV, thisV, tzV]
          .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := hp' })
        | "PeriodUntilKt$progressivePeriodUntil$4$1", "<init>",
            _cont :: thisV :: clockV :: listV :: .allocRef _ :: .allocRef _ :: rest =>
          let (cid, hp') :=
            allocClosure st.heap "PeriodUntilKt$progressivePeriodUntil$4$1" [listV, clockV, thisV]
          .inl (some { st with pc := st.pc + 1, stack := .ext (.closureRef cid) :: rest, heap := hp' })
        | _, _, _ => .inr none
      stepInvokeVirtual := fun st cls method desc =>
        match normalizeTimeClass cls, method, desc, st.stack with
        | "kotlinx/datetime/DateTimePeriod", "getYears", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.years.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getMonths", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.months.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getDays", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.days.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getHours", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.hours.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getMinutes", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.minutes.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getSeconds", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.seconds.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimePeriod", "getNanoseconds", "()I", .ext (.period p) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 p.nanoseconds.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimeUnit$TimeBased", "getNanoseconds", "()J",
            .ext (.timeUnit (.timeBased u)) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i64 u.nanoseconds.toUInt64 :: rest })
        | "kotlinx/datetime/DateTimeUnit$DayBased", "getDays", "()I",
            .ext (.timeUnit (.dateBased (.dayBased d))) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 d.toUInt32 :: rest })
        | "kotlinx/datetime/DateTimeUnit$MonthBased", "getMonths", "()I",
            .ext (.timeUnit (.dateBased (.monthBased m))) :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 m.toUInt32 :: rest })
        | "kotlin/Pair", "component1", _, .pair a _ :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := a :: rest })
        | "kotlin/Pair", "component2", _, .pair _ b :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := b :: rest })
        | "androidx/compose/runtime/Composer$Companion", "getEmpty", _,
            .ext (.companion "androidx/compose/runtime/Composer$Companion") :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .ext .composerEmpty :: rest })
        | _, _, _, _ => .inr none
      stepInvokeStatic := fun st cls method desc =>
        let nCls := normalizeTimeClass cls
        if nCls == "PeriodUntilKt" then
          let nArgs := (Jvm.parseMethodParamTags desc).length
          if st.stack.length < nArgs then .inr none
          else
            let popped := st.stack.take nArgs
            let rest := st.stack.drop nArgs
            let fnTag := nCls ++ "." ++ method ++ ":" ++ desc
            match invokeProg st fnTag desc popped.reverse with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
        else
        match nCls, method, desc, st.stack with
        | "kotlin/time/DurationKt", "toDuration", "(ILkotlin/time/DurationUnit;)J",
            .ext (.durationUnit u) :: v :: rest =>
          match v.asI32? with
          | some iv =>
            let dur := Model.Duration.ofIntUnit iv.toInt32 u
            .inl (some { st with pc := st.pc + 1, stack := .i64 dur.rawValue.toUInt64 :: rest })
          | none => .inr none
        | "kotlin/time/DurationKt", "toDuration", "(JLkotlin/time/DurationUnit;)J",
            .ext (.durationUnit u) :: v :: rest =>
          match v.asI64? with
          | some lv =>
            let dur := Model.Duration.ofLongUnit lv.toInt64 u
            .inl (some { st with pc := st.pc + 1, stack := .i64 dur.rawValue.toUInt64 :: rest })
          | none => .inr none
        | "kotlin/time/DurationKt", "toDuration", "(DLkotlin/time/DurationUnit;)J",
            .ext (.durationUnit .days) :: v :: rest =>
          match v.asF64? with
          | some dv =>
            match Model.Duration.ofDaysFloat? dv with
            | some dur => .inl (some { st with pc := st.pc + 1, stack := .i64 dur.rawValue.toUInt64 :: rest })
            | none => .inr none
          | none => .inr none
        | "kotlin/time/Duration", "getInWholeNanoseconds-impl", "(J)J", v :: rest =>
          match v.asI64? with
          | some lv =>
            let ns := (Model.Duration.mk lv.toInt64).inWholeNanoseconds
            .inl (some { st with pc := st.pc + 1, stack := .i64 ns.toUInt64 :: rest })
          | none => .inr none
        | "kotlin/time/Duration", "plus-LRDsOJo", "(JJ)J", b :: a :: rest =>
          match a.asI64?, b.asI64? with
          | some la, some lb =>
            match Model.Duration.plus? ⟨la.toInt64⟩ ⟨lb.toInt64⟩ with
            | some dur => .inl (some { st with pc := st.pc + 1, stack := .i64 dur.rawValue.toUInt64 :: rest })
            | none => .inr none
          | _, _ => .inr none
        | "kotlinx/datetime/InstantKt", "until",
            "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit;Lkotlinx/datetime/TimeZone;)J",
            .ext (.timeZone tz) :: .ext (.timeUnit u) :: .ext (.instant other) :: .ext (.instant start) :: rest =>
          let v := st.heap.untilTz start other u tz
          .inl (some { st with pc := st.pc + 1, stack := .i64 v.toUInt64 :: rest })
        | "kotlinx/datetime/InstantKt", "until",
            "(Lkotlin/time/Instant;Lkotlin/time/Instant;Lkotlinx/datetime/DateTimeUnit$TimeBased;)J",
            .ext (.timeUnit (.timeBased tu)) :: .ext (.instant other) :: .ext (.instant start) :: rest =>
          let v := st.heap.untilTime start other tu
          .inl (some { st with pc := st.pc + 1, stack := .i64 v.toUInt64 :: rest })
        | "kotlinx/datetime/DateTimePeriodKt", "DateTimePeriod$default", _,
            _marker :: maskV :: nsV :: secV :: minV :: hrV :: dayV :: monV :: yrV :: rest =>
          match maskV.asI32?, nsV.asI64?, secV.asI32?, minV.asI32?,
              hrV.asI32?, dayV.asI32?, monV.asI32?, yrV.asI32? with
          | some mask, some ns, some sec, some min, some hr, some day, some mon, some yr =>
            let p := applyDateTimePeriodDefault mask yr mon day hr min sec ns
            .inl (some { st with pc := st.pc + 1, stack := .ext (.period p) :: rest })
          | _, _, _, _, _, _, _, _ => .inr none
        | "kotlin/TuplesKt", "to", _, b :: a :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
        | "java/lang/Math", "abs", "(J)J", v :: rest =>
          match v.asI64? with
          | some lv =>
            let res : UInt64 := if lv.toBitVec.slt 0#64 then -lv else lv
            .inl (some { st with pc := st.pc + 1, stack := .i64 res :: rest })
          | none => .inr none
        | "java/lang/Math", "abs", "(I)I", v :: rest =>
          match v.asI32? with
          | some iv =>
            let res : UInt32 := if iv.toBitVec.slt 0#32 then -iv else iv
            .inl (some { st with pc := st.pc + 1, stack := .i32 res :: rest })
          | none => .inr none
        | "kotlin/collections/CollectionsKt", "last", _, .heapRef colAddr :: rest =>
          match Jvm.extractListArray? st.jvmHeap colAddr with
          | some elems =>
            if h : 0 < elems.size then
              .inl (some { st with pc := st.pc + 1, stack := elems[elems.size - 1] :: rest })
            else .inr none
          | none => .inr none
        | "androidx/compose/runtime/ComposerKt", "sourceInformation", _, _info :: .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerStart", _,
            _info :: _key :: .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "sourceInformationMarkerEnd", _, .ext .composer :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "isTraceInProgress", "()Z", rest =>
          let v : UInt32 := if st.heap.composer.traceEnabled then 1 else 0
          .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventStart", _, _s :: _d :: _c :: _k :: rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/ComposerKt", "traceEventEnd", "()V", rest =>
          .inl (some { st with pc := st.pc + 1, stack := rest })
        | "androidx/compose/runtime/SnapshotStateKt", "produceState", _,
            _changed :: .ext .composer :: _producer :: initialVal :: rest =>
          let (sid, comp') := Compose.allocState st.heap.composer initialVal
          .inl (some { st with
            pc := st.pc + 1
            stack := .ext (.stateRef sid) :: rest
            heap := { st.heap with composer := comp' }
          })
        | nCls, method, desc, stackNow =>
          let nArgs := (Jvm.parseMethodParamTags desc).length
          if stackNow.length < nArgs then .inr none
          else
            let popped := stackNow.take nArgs
            let rest := stackNow.drop nArgs
            let fnTag := nCls ++ "." ++ method ++ ":" ++ desc
            match invokeProg st fnTag desc popped.reverse with
            | some (res, st') => .inl (some { st' with pc := st.pc + 1, stack := res :: rest })
            | none => .inr none
      stepInvokeInterface := fun st cls method desc =>
        match stepComposerInterface st method desc with
        | .inl (some st') => .inl (some st')
        | .inl none => .inr none
        | .inr (some res) => .inr (some res)
        | .inr none =>
          match cls, method, st.stack with
          | "kotlin/time/Clock", "now", .ext (.clock _) :: rest =>
            let ns := st.heap.clockNow st.heap.clockReads
            let hp' := { st.heap with clockReads := st.heap.clockReads + 1 }
            .inl (some { st with pc := st.pc + 1, stack := .ext (.instant ns) :: rest, heap := hp' })
          | "androidx/compose/runtime/State", "getValue", .ext (.stateRef sid) :: rest =>
            match Compose.readState st.heap.composer sid with
            | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
            | none => .inr none
          | _, _, _ => .inr none
    }

/-- Default leaf hooks for methods without nested `PeriodUntilKt` calls. -/
def timeHooks : Jvm.JvmHooks TimeExt TimeHeap :=
  mkTimeHooks (fun _ => none) 4 64

abbrev runJvm (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option JvmVal :=
  Jvm.runJvm timeHooks fuel prog st

abbrev runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  Jvm.runJvmRes timeHooks fuel prog st

end TimeUtil.JvmVerification

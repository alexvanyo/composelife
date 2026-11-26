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
import SessionValue.Basic
import SessionValue.StateMachine

namespace SessionValue.JvmVerification

export Jvm (JvmInstr setLocal)

inductive SvExt where
  | uuid (u : Uuid)
  | obj (v : Nat)
  | sv (v : SessionValue Nat)
  | info (i : LocalSessionInfo)
  | st (s : State Nat)
  | fn (f : Nat → Nat)
  deriving Inhabited

abbrev JvmVal := Jvm.JvmVal SvExt
abbrev JvmState := Jvm.JvmState SvExt Unit

namespace JvmVal
export Jvm.JvmVal (i32 i64 f64 bool null unit uninit str allocRef pair ext isNull asI32? asI64? asF32? asF64?)

def isTruthy : JvmVal → Bool
  | .bool b => b
  | .i32 v => v != 0
  | _ => false

def isActive : JvmVal → Bool
  | .ext (.info (.active ..)) => true
  | _ => false

def isInactive : JvmVal → Bool
  | .ext (.info (.inactive ..)) => true
  | _ => false

def beqExt : SvExt → SvExt → Bool
  | .uuid a, .uuid b => a == b
  | .obj a, .obj b => a == b
  | _, _ => false

def beqVal (a b : JvmVal) : Bool :=
  Jvm.JvmVal.beqVal beqExt a b

@[simp] theorem beqVal_uuid (a b : Uuid) :
    Jvm.JvmVal.beqVal beqExt (.ext (.uuid a)) (.ext (.uuid b)) = (a == b) := rfl

@[simp] theorem beqVal_obj (a b : Nat) :
    Jvm.JvmVal.beqVal beqExt (.ext (.obj a)) (.ext (.obj b)) = (a == b) := rfl

@[simp] theorem beqVal_bool (a b : Bool) :
    Jvm.JvmVal.beqVal beqExt (.bool a) (.bool b) = (a == b) := rfl

def ite (c : Bool) (t e : Option JvmVal) : Option JvmVal :=
  match t, e with
  | some (.ext (.st a)), some (.ext (.st b)) =>
    some (.ext (.st ⟨
      if c then a.upstreamSessionIdBeforeLocalSession else b.upstreamSessionIdBeforeLocalSession,
      if c then a.upstreamSessionValue else b.upstreamSessionValue,
      if c then a.localSessionId else b.localSessionId,
      if c then a.localSessionValue else b.localSessionValue
    ⟩))
  | some (.ext (.sv a)), some (.ext (.sv b)) => some (.ext (.sv (if c then a else b)))
  | some (.ext (.info a)), some (.ext (.info b)) => some (.ext (.info (if c then a else b)))
  | some (.bool a), some (.bool b) => some (.bool (if c then a else b))
  | some (.ext (.uuid a)), some (.ext (.uuid b)) => some (.ext (.uuid (if c then a else b)))
  | _, _ => if c then t else e

end JvmVal

def initJvmState (slots : List (Nat × JvmVal)) : JvmState :=
  Jvm.initJvmState slots .null ()

def optSvToVal : Option (SessionValue Nat) → JvmVal
  | none => .null
  | some s => .ext (.sv s)

def valToOptSv : JvmVal → Option (SessionValue Nat)
  | .ext (.sv s) => some s
  | _ => none

def checkOptSv : JvmVal → Option (Option (SessionValue Nat))
  | .null => some none
  | .ext (.sv s) => some (some s)
  | _ => none

def svHooks : Jvm.JvmHooks SvExt Unit where
  beqExt := JvmVal.beqExt
  iteVal := JvmVal.ite
  isZero? := fun v => match v with
    | .bool b => some (!b)
    | .i32 x => some (x == 0)
    | _ => none
  iteZero? := fun v jump fall => match v with
    | .bool b => JvmVal.ite (!b) jump fall
    | .i32 x => JvmVal.ite (x == 0) jump fall
    | _ => none
  iteNonZero? := fun v jump fall => match v with
    | .bool b => JvmVal.ite b jump fall
    | .i32 x => JvmVal.ite (!(x == 0)) jump fall
    | _ => none
  ireturnVal := fun v => .bool (JvmVal.isTruthy v)
  stepNewClass := fun st _ => .inl (some { st with pc := st.pc + 1, stack := .uninit :: st.stack })
  checkInstanceOf :=
    let base := Jvm.defaultCheckInstanceOf fun cls ext =>
      match cls, ext with
      | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo", .info _ => true
      | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Active", .info (.active ..) => true
      | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Inactive", .info (.inactive ..) => true
      | "com/alexvanyo/composelife/sessionvalue/SessionValue", .sv _ => true
      | "com/alexvanyo/composelife/sessionvalue/SessionValueState", .st _ => true
      | _, _ => false
    fun cls v =>
      match v with
      | .null => false
      | .uninit => false
      | _ => base cls v
  checkCast := fun cls v =>
    match cls, v with
    | _, .null => some .null
    | "java/lang/Object", .uninit => none
    | "java/lang/Object", _ => some v
    | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo", .ext (.info _) => some v
    | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Active", .ext (.info (.active ..)) => some v
    | "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Inactive", .ext (.info (.inactive ..)) => some v
    | "com/alexvanyo/composelife/sessionvalue/SessionValue", .ext (.sv _) => some v
    | "com/alexvanyo/composelife/sessionvalue/SessionValueState", .ext (.st _) => some v
    | "kotlin/Pair", .pair _ _ => some v
    | _, _ => none
  stepInvokeVirtual := fun st _cls method _desc =>
    match st.stack with
    | recv :: rest =>
      if method == "getSessionId" then
        match recv with
        | .ext (.sv v) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid v.sessionId) :: rest })
        | _ => .inr none
      else if method == "getValueId" then
        match recv with
        | .ext (.sv v) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid v.valueId) :: rest })
        | _ => .inr none
      else if method == "getValue" then
        match recv with
        | .ext (.sv v) => .inl (some { st with pc := st.pc + 1, stack := .ext (.obj v.value) :: rest })
        | _ => .inr none
      else if method == "getCurrentLocalSessionId" then
        match recv with
        | .ext (.info (.active cur _ _)) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid cur) :: rest })
        | _ => .inr none
      else if method == "getPreviousUpstreamSessionId" then
        match recv with
        | .ext (.info (.active _ _ prev)) =>
          .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid prev) :: rest })
        | _ => .inr none
      else if method == "getNextLocalSessionId" then
        match recv with
        | .ext (.info (.inactive _ nxt)) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid nxt) :: rest })
        | _ => .inr none
      else if method == "getCurrentUpstreamSessionId" then
        match recv with
        | .ext (.info (.inactive cur _)) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid cur) :: rest })
        | _ => .inr none
      else if method == "getUpstreamSessionIdBeforeLocalSession" then
        match recv with
        | .ext (.st s) =>
          .inl (some {
            st with
            pc := st.pc + 1
            stack := .ext (.uuid s.upstreamSessionIdBeforeLocalSession) :: rest
          })
        | _ => .inr none
      else if method == "getUpstreamSessionValue" then
        match recv with
        | .ext (.st s) => .inl (some { st with pc := st.pc + 1, stack := .ext (.sv s.upstreamSessionValue) :: rest })
        | _ => .inr none
      else if method == "getLocalSessionId" then
        match recv with
        | .ext (.st s) => .inl (some { st with pc := st.pc + 1, stack := .ext (.uuid s.localSessionId) :: rest })
        | _ => .inr none
      else if method == "getLocalSessionValue" then
        match recv with
        | .ext (.st s) => .inl (some { st with pc := st.pc + 1, stack := optSvToVal s.localSessionValue :: rest })
        | _ => .inr none
      else
        .inr none
    | _ => .inr none
  stepInvokeSpecial := fun st cls method _desc =>
    if method != "<init>" then .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/SessionValue" then
      match st.stack with
      | .ext (.obj v) :: .ext (.uuid vid) :: .ext (.uuid sid) :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .ext (.sv ⟨sid, vid, v⟩) :: rest })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Inactive" then
      match st.stack with
      | .ext (.uuid nxt) :: .ext (.uuid cur) :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .ext (.info (.inactive cur nxt)) :: rest })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Active" then
      match st.stack with
      | .ext (.uuid prev) :: upVal :: .ext (.uuid cur) :: .uninit :: .uninit :: rest =>
        .inl (some {
          st with
          pc := st.pc + 1
          stack := .ext (.info (.active cur (JvmVal.isTruthy upVal) prev)) :: rest
        })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/SessionValueState" then
      match st.stack with
      | lv :: .ext (.uuid lid) :: .ext (.sv uv) :: .ext (.uuid ub) :: .uninit :: .uninit :: rest =>
        match checkOptSv lv with
        | some optLv =>
          let constructed : State Nat := ⟨ub, uv, lid, optLv⟩
          .inl (some { st with pc := st.pc + 1, stack := .ext (.st constructed) :: rest })
        | none => .inr none
      | _ => .inr none
    else
      .inr none
  stepInvokeStatic := fun st _cls method _desc =>
    if method == "f_SessionValue_State_sessionValue___redArg" then
      match st.stack with
      | .ext (.st s) :: rest => .inl (some { st with pc := st.pc + 1, stack := .ext (.sv s.sessionValue) :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_stepSetValue___redArg" then
      match st.stack with
      | .ext (.uuid vid) :: .ext (.obj v) :: .ext (.st s) :: rest =>
        let res := SessionValue.stepSetValue s v vid
        let out := Jvm.JvmVal.pair (.ext (.st res.1)) (.pair (.ext (.sv res.2.1)) (.ext (.sv res.2.2)))
        .inl (some { st with pc := st.pc + 1, stack := out :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_stepSetValueFromUpstream___redArg" then
      match st.stack with
      | .ext (.uuid fresh) :: .ext (.sv newUpstream) :: .ext (.st s) :: rest =>
        .inl (some {
          st with
          pc := st.pc + 1
          stack := .ext (.st (SessionValue.stepSetValueFromUpstream s newUpstream fresh)) :: rest
        })
      | _ => .inr none
    else if method == "f_SessionValue_LocalSessionInfo_isCurrentSessionUpdate___redArg" then
      match st.stack with
      | .ext (.sv newVal) :: .ext (.info i) :: rest =>
        .inl (some {
          st with
          pc := st.pc + 1
          stack := .bool (LocalSessionInfo.isCurrentSessionUpdate i newVal) :: rest
        })
      | _ => .inr none
    else
      .inr none
  stepInvokeInterface := fun st _cls method _desc =>
    if method == "invoke" then
      match st.stack with
      | .ext (.obj x) :: .ext (.fn f) :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .ext (.obj (f x)) :: rest })
      | _ => .inr none
    else
      .inr none

def stepInstr := Jvm.stepInstr svHooks
def runJvm := Jvm.runJvm svHooks

@[simp] theorem svHooks_beqExt_uuid (a b : Uuid) :
    Jvm.JvmVal.beqVal svHooks.beqExt (.ext (.uuid a)) (.ext (.uuid b)) = (a == b) := rfl

@[simp] theorem svHooks_beqExt_obj (a b : Nat) :
    Jvm.JvmVal.beqVal svHooks.beqExt (.ext (.obj a)) (.ext (.obj b)) = (a == b) := rfl

@[simp] theorem svHooks_beqExt_bool (a b : Bool) :
    Jvm.JvmVal.beqVal svHooks.beqExt (.bool a) (.bool b) = (a == b) := rfl

end SessionValue.JvmVerification

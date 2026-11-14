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

import SessionValue.Basic
import SessionValue.StateMachine

namespace SessionValue.JvmVerification

inductive JvmVal where
  | null
  | uninit
  | bool (b : Bool)
  | i32 (v : UInt32)
  | str (s : String)
  | uuid (u : Uuid)
  | obj (v : Nat)
  | sv (v : SessionValue Nat)
  | info (i : LocalSessionInfo)
  | st (s : State Nat)
  | pair (fst snd : JvmVal)
  | fn (f : Nat → Nat)
  deriving Inhabited

def JvmVal.isNull : JvmVal → Bool
  | .null => true
  | _ => false

def JvmVal.isTruthy : JvmVal → Bool
  | .bool b => b
  | .i32 v => v != 0
  | _ => false

def JvmVal.isActive : JvmVal → Bool
  | .info (.active ..) => true
  | _ => false

def JvmVal.isInactive : JvmVal → Bool
  | .info (.inactive ..) => true
  | _ => false

def JvmVal.beqVal : JvmVal → JvmVal → Bool
  | .uuid a, .uuid b => a == b
  | .bool a, .bool b => a == b
  | .obj a, .obj b => a == b
  | _, _ => false

def JvmVal.ite (c : Bool) (t e : Option JvmVal) : Option JvmVal :=
  match t, e with
  | some (.st a), some (.st b) =>
    some (.st ⟨if c then a.upstreamSessionIdBeforeLocalSession else b.upstreamSessionIdBeforeLocalSession,
      if c then a.upstreamSessionValue else b.upstreamSessionValue,
      if c then a.localSessionId else b.localSessionId,
      if c then a.localSessionValue else b.localSessionValue⟩)
  | some (.sv a), some (.sv b) => some (.sv (if c then a else b))
  | some (.info a), some (.info b) => some (.info (if c then a else b))
  | some (.bool a), some (.bool b) => some (.bool (if c then a else b))
  | some (.uuid a), some (.uuid b) => some (.uuid (if c then a else b))
  | _, _ => if c then t else e

inductive JvmInstr where
  | nop | dup | pop | swap | aconstNull | athrow
  | iconst (v : UInt32)
  | lconst (v : UInt64)
  | dconst0 | dconst1
  | ldcStr (s : String)
  | iload (idx : Nat)
  | lload (idx : Nat)
  | aload (idx : Nat)
  | dload (idx : Nat)
  | istore (idx : Nat)
  | lstore (idx : Nat)
  | astore (idx : Nat)
  | dstore (idx : Nat)
  | iadd | isub | imul | ineg | iand | ior | ixor | ishl | ishr | iushr
  | ladd | lsub | lmul | land | lor | lxor | lshl | lshr | lushr
  | dneg | dcmpg | dcmpl
  | i2l | l2i | i2b | lcmp
  | ifeq (target : Nat)
  | ifne (target : Nat)
  | iflt (target : Nat)
  | ifle (target : Nat)
  | ifgt (target : Nat)
  | ifge (target : Nat)
  | ifnull (target : Nat)
  | ifnonnull (target : Nat)
  | if_icmpeq (target : Nat)
  | if_icmpne (target : Nat)
  | if_icmplt (target : Nat)
  | goto (target : Nat)
  | newClass (cls : String)
  | checkcast (cls : String)
  | instanceof (cls : String)
  | invokevirtual (cls method desc : String)
  | invokespecial (cls method desc : String)
  | invokestatic (cls method desc : String)
  | invokeinterface (cls method desc : String)
  | getfield (cls field desc : String)
  | ireturn | lreturn | areturn | dreturn | vreturn
  deriving Repr, Inhabited

structure JvmState where
  pc : Nat
  stack : List JvmVal
  locals : Nat → JvmVal

def setLocal (locals : Nat → JvmVal) (idx : Nat) (v : JvmVal) : Nat → JvmVal :=
  fun i => if i = idx then v else locals i

def initJvmState (slots : List (Nat × JvmVal)) : JvmState where
  pc := 0
  stack := []
  locals := slots.foldl (fun loc (idx, v) => setLocal loc idx v) (fun _ => .null)

def optSvToVal : Option (SessionValue Nat) → JvmVal
  | none => .null
  | some s => .sv s

def valToOptSv : JvmVal → Option (SessionValue Nat)
  | .sv s => some s
  | _ => none

def stepInstr (instr : JvmInstr) (st : JvmState) : Option JvmState ⊕ Option JvmVal :=
  match instr with
  | .nop => .inl (some { st with pc := st.pc + 1 })
  | .dup =>
    match st.stack with
    | v :: rest => .inl (some { st with pc := st.pc + 1, stack := v :: v :: rest })
    | _ => .inr none
  | .pop =>
    match st.stack with
    | _ :: rest => .inl (some { st with pc := st.pc + 1, stack := rest })
    | _ => .inr none
  | .swap =>
    match st.stack with
    | a :: b :: rest => .inl (some { st with pc := st.pc + 1, stack := b :: a :: rest })
    | _ => .inr none
  | .aconstNull => .inl (some { st with pc := st.pc + 1, stack := .null :: st.stack })
  | .iconst v => .inl (some { st with pc := st.pc + 1, stack := .i32 v :: st.stack })
  | .ldcStr s => .inl (some { st with pc := st.pc + 1, stack := .str s :: st.stack })
  | .aload idx | .iload idx =>
    .inl (some { st with pc := st.pc + 1, stack := st.locals idx :: st.stack })
  | .astore idx | .istore idx =>
    match st.stack with
    | v :: rest => .inl (some { pc := st.pc + 1, stack := rest, locals := setLocal st.locals idx v })
    | _ => .inr none
  | .newClass _ => .inl (some { st with pc := st.pc + 1, stack := .uninit :: st.stack })
  | .checkcast _ => .inl (some { st with pc := st.pc + 1 })
  | .instanceof cls =>
    match st.stack with
    | v :: rest =>
      let b :=
        if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Active" then v.isActive
        else if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Inactive" then v.isInactive
        else false
      .inl (some { st with pc := st.pc + 1, stack := .bool b :: rest })
    | _ => .inr none
  | .invokevirtual _ method _ =>
    match st.stack with
    | recv :: rest =>
      if method == "getSessionId" then
        match recv with
        | .sv v => .inl (some { st with pc := st.pc + 1, stack := .uuid v.sessionId :: rest })
        | _ => .inr none
      else if method == "getValueId" then
        match recv with
        | .sv v => .inl (some { st with pc := st.pc + 1, stack := .uuid v.valueId :: rest })
        | _ => .inr none
      else if method == "getValue" then
        match recv with
        | .sv v => .inl (some { st with pc := st.pc + 1, stack := .obj v.value :: rest })
        | _ => .inr none
      else if method == "getCurrentLocalSessionId" then
        match recv with
        | .info (.active cur _ _) => .inl (some { st with pc := st.pc + 1, stack := .uuid cur :: rest })
        | _ => .inr none
      else if method == "getPreviousUpstreamSessionId" then
        match recv with
        | .info (.active _ _ prev) => .inl (some { st with pc := st.pc + 1, stack := .uuid prev :: rest })
        | _ => .inr none
      else if method == "getNextLocalSessionId" then
        match recv with
        | .info (.inactive _ nxt) => .inl (some { st with pc := st.pc + 1, stack := .uuid nxt :: rest })
        | _ => .inr none
      else if method == "getCurrentUpstreamSessionId" then
        match recv with
        | .info (.inactive cur _) => .inl (some { st with pc := st.pc + 1, stack := .uuid cur :: rest })
        | _ => .inr none
      else if method == "getUpstreamSessionIdBeforeLocalSession" then
        match recv with
        | .st s => .inl (some { st with pc := st.pc + 1, stack := .uuid s.upstreamSessionIdBeforeLocalSession :: rest })
        | _ => .inr none
      else if method == "getUpstreamSessionValue" then
        match recv with
        | .st s => .inl (some { st with pc := st.pc + 1, stack := .sv s.upstreamSessionValue :: rest })
        | _ => .inr none
      else if method == "getLocalSessionId" then
        match recv with
        | .st s => .inl (some { st with pc := st.pc + 1, stack := .uuid s.localSessionId :: rest })
        | _ => .inr none
      else if method == "getLocalSessionValue" then
        match recv with
        | .st s => .inl (some { st with pc := st.pc + 1, stack := optSvToVal s.localSessionValue :: rest })
        | _ => .inr none
      else if method == "getFirst" then
        match recv with
        | .pair a _ => .inl (some { st with pc := st.pc + 1, stack := a :: rest })
        | _ => .inr none
      else if method == "getSecond" then
        match recv with
        | .pair _ b => .inl (some { st with pc := st.pc + 1, stack := b :: rest })
        | _ => .inr none
      else
        .inr none
    | _ => .inr none
  | .invokespecial cls "<init>" _ =>
    if cls == "com/alexvanyo/composelife/sessionvalue/SessionValue" then
      match st.stack with
      | .obj v :: .uuid vid :: .uuid sid :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .sv ⟨sid, vid, v⟩ :: rest })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Inactive" then
      match st.stack with
      | .uuid nxt :: .uuid cur :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .info (.inactive cur nxt) :: rest })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/LocalSessionInfo$Active" then
      match st.stack with
      | .uuid prev :: upVal :: .uuid cur :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .info (.active cur upVal.isTruthy prev) :: rest })
      | _ => .inr none
    else if cls == "com/alexvanyo/composelife/sessionvalue/SessionValueState" then
      match st.stack with
      | lv :: .uuid lid :: .sv uv :: .uuid ub :: .uninit :: .uninit :: rest =>
        let constructed : State Nat := ⟨ub, uv, lid, valToOptSv lv⟩
        .inl (some { st with pc := st.pc + 1, stack := .st constructed :: rest })
      | _ => .inr none
    else if cls == "kotlin/Pair" then
      match st.stack with
      | b :: a :: .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .pair a b :: rest })
      | _ => .inr none
    else if cls == "kotlin/NoWhenBranchMatchedException" then
      match st.stack with
      | .uninit :: .uninit :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .null :: rest })
      | _ => .inr none
    else
      .inr none
  | .invokeinterface _ "invoke" _ =>
    match st.stack with
    | .obj x :: .fn f :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .obj (f x) :: rest })
    | _ => .inr none
  | .invokestatic _ method _ =>
    if method == "checkNotNullParameter" || method == "checkNotNull" then
      match st.stack with
      | .str _ :: _ :: rest => .inl (some { st with pc := st.pc + 1, stack := rest })
      | _ => .inr none
    else if method == "areEqual" then
      match st.stack with
      | b :: a :: rest => .inl (some { st with pc := st.pc + 1, stack := .bool (JvmVal.beqVal a b) :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_State_sessionValue___redArg" then
      match st.stack with
      | .st s :: rest => .inl (some { st with pc := st.pc + 1, stack := .sv s.sessionValue :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_stepSetValue___redArg" then
      match st.stack with
      | .uuid vid :: .obj v :: .st s :: rest =>
        let res := SessionValue.stepSetValue s v vid
        let out := JvmVal.pair (.st res.1) (.pair (.sv res.2.1) (.sv res.2.2))
        .inl (some { st with pc := st.pc + 1, stack := out :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_stepSetValueFromUpstream___redArg" then
      match st.stack with
      | .uuid fresh :: .sv newUpstream :: .st s :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .st (SessionValue.stepSetValueFromUpstream s newUpstream fresh) :: rest })
      | _ => .inr none
    else if method == "f_SessionValue_LocalSessionInfo_isCurrentSessionUpdate___redArg" then
      match st.stack with
      | .sv newVal :: .info i :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := .bool (LocalSessionInfo.isCurrentSessionUpdate i newVal) :: rest })
      | _ => .inr none
    else
      .inr none
  | .goto target => .inl (some { st with pc := target })
  | .areturn =>
    match st.stack with
    | v :: _ => .inr (some v)
    | _ => .inr none
  | .ireturn =>
    match st.stack with
    | v :: _ => .inr (some (.bool v.isTruthy))
    | _ => .inr none
  | _ => .inr none

def runJvm : Nat → List JvmInstr → JvmState → Option JvmVal
  | 0, _, _ => none
  | fuel + 1, prog, st =>
    match prog[st.pc]? with
    | none => none
    | some (.ifeq target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite v.isTruthy
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
          (runJvm fuel prog { st with pc := target, stack := rest })
      | _ => none
    | some (.ifne target) =>
      match st.stack with
      | v :: rest =>
        JvmVal.ite v.isTruthy
          (runJvm fuel prog { st with pc := target, stack := rest })
          (runJvm fuel prog { st with pc := st.pc + 1, stack := rest })
      | _ => none
    | some (.ifnonnull target) =>
      match st.stack with
      | v :: rest =>
        if v.isNull then
          runJvm fuel prog { st with pc := st.pc + 1, stack := rest }
        else
          runJvm fuel prog { st with pc := target, stack := rest }
      | _ => none
    | some instr =>
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res

end SessionValue.JvmVerification

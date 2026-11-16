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

import JvmSemantics
import JvmBytecode
import Jvm.Audit

namespace SessionValue.JvmVerification

open SessionValue.JvmBytecode

theorem svMap_equiv (sv : SessionValue Nat) (f : Nat → Nat) :
    runJvm 30 f_SessionValue_SessionValue_map___redArg_prog
        (initJvmState [(0, .ext (.sv sv)), (1, .ext (.fn f))]) =
      some (.ext (.sv (sv.map f))) := by
  rfl

theorem getLocalSessionId_equiv (info : LocalSessionInfo) :
    runJvm 30 getLocalSessionId_prog (initJvmState [(0, .ext (.info info))]) =
      some (.ext (.uuid info.localSessionId)) := by
  cases info <;> rfl

theorem getPreLocalSessionId_equiv (info : LocalSessionInfo) :
    runJvm 30 getPreLocalSessionId_prog (initJvmState [(0, .ext (.info info))]) =
      some (.ext (.uuid info.preLocalSessionId)) := by
  cases info <;> rfl

theorem isLocalSessionActive_equiv (info : LocalSessionInfo) :
    runJvm 30 isLocalSessionActive_prog (initJvmState [(0, .ext (.info info))]) =
      some (.bool info.isLocalSessionActive) := by
  cases info <;> rfl

theorem stateSessionValue_equiv (st : State Nat) :
    runJvm 30 f_SessionValue_State_sessionValue___redArg_prog (initJvmState [(0, .ext (.st st))]) =
      some (.ext (.sv st.sessionValue)) := by
  rcases st with ⟨_, _, _, _ | lv⟩ <;> rfl

theorem stateInfo_equiv (st : State Nat) :
    runJvm 60 f_SessionValue_State_info___redArg_prog (initJvmState [(0, .ext (.st st))]) =
      some (.ext (.info st.info)) := by
  rcases st with ⟨ub, uv, lid, _ | lv⟩
  · rfl
  · change some (JvmVal.ext (SvExt.info _)) = some (JvmVal.ext (SvExt.info _))
    congr 3
    by_cases h1 : (uv.sessionId == lv.sessionId) = true <;>
      by_cases h2 : (uv.valueId == lv.valueId) = true <;>
      simp [setLocal, JvmVal.isTruthy, SessionValue.State.info, h1, h2]

theorem stepSetValue_redArg_equiv (st : State Nat) (v : Nat) (vid : Uuid) :
    runJvm 50 f_SessionValue_stepSetValue___redArg_prog
      (initJvmState [(0, .ext (.st st)), (1, .ext (.obj v)), (2, .ext (.uuid vid))]) =
      let res := SessionValue.stepSetValue st v vid
      some (.pair (.ext (.st res.1)) (.pair (.ext (.sv res.2.1)) (.ext (.sv res.2.2)))) := by
  rfl

theorem stepSetValue_equiv (st : State Nat) (v : Nat) (vid : Uuid) :
    runJvm 80 stepSetValue_prog
      (initJvmState [(0, .ext (.st st)), (1, .ext (.obj v)), (2, .ext (.uuid vid))]) =
      let res := SessionValue.stepSetValue st v vid
      some (.pair (.ext (.st res.1)) (.pair (.ext (.sv res.2.1)) (.ext (.sv res.2.2)))) := by
  rfl

theorem isCurrentSessionUpdate_redArg_equiv (info : LocalSessionInfo) (newVal : SessionValue Nat) :
    runJvm 30 f_SessionValue_LocalSessionInfo_isCurrentSessionUpdate___redArg_prog
      (initJvmState [(0, .ext (.info info)), (1, .ext (.sv newVal))]) =
      some (.bool (info.isCurrentSessionUpdate newVal)) := by
  cases info <;> rfl

theorem isCurrentSessionUpdate_equiv (info : LocalSessionInfo) (newVal : SessionValue Nat) :
    runJvm 30 isCurrentSessionUpdate_prog
      (initJvmState [(0, .ext (.info info)), (1, .ext (.sv newVal))]) =
      some (.bool (info.isCurrentSessionUpdate newVal)) := by
  rfl

theorem stepSetValueFromUpstream_redArg_equiv (st : State Nat) (newUp : SessionValue Nat) (fresh : Uuid) :
    runJvm 140 f_SessionValue_stepSetValueFromUpstream___redArg_prog
      (initJvmState [(0, .ext (.st st)), (1, .ext (.sv newUp)), (2, .ext (.uuid fresh))]) =
      some (.ext (.st (SessionValue.stepSetValueFromUpstream st newUp fresh))) := by
  rcases st with ⟨ub, uv, lid, _ | lv⟩
  · change some (JvmVal.ext (SvExt.st _)) = some (JvmVal.ext (SvExt.st _))
    congr 3
    by_cases hSid : newUp.sessionId = uv.sessionId <;>
      by_cases hVid : newUp.valueId = uv.valueId <;>
      by_cases hFresh : fresh = newUp.sessionId <;>
      simp [initJvmState, Jvm.initJvmState, setLocal, List.foldl,
        SessionValue.stepSetValueFromUpstream, bne,
        hSid, hVid, hFresh]
  · change some (JvmVal.ext (SvExt.st _)) = some (JvmVal.ext (SvExt.st _))
    congr 3
    have hSymm : (lv.sessionId = uv.sessionId) ↔ (uv.sessionId = lv.sessionId) := eq_comm
    by_cases hSid : newUp.sessionId = uv.sessionId <;>
      by_cases hVid : newUp.valueId = uv.valueId <;>
      by_cases hLvSid : newUp.sessionId = lv.sessionId <;>
      by_cases hFresh : fresh = newUp.sessionId <;>
      by_cases hStSid : lid = newUp.sessionId <;>
      by_cases hUvLvSid : uv.sessionId = lv.sessionId <;>
      simp [initJvmState, Jvm.initJvmState, setLocal, List.foldl,
        SessionValue.stepSetValueFromUpstream, bne,
        hSymm, hSid, hVid, hLvSid, hFresh, hStSid, hUvLvSid]

theorem stepSetValueFromUpstream_equiv (st : State Nat) (newUp : SessionValue Nat) (fresh : Uuid) :
    runJvm 30 stepSetValueFromUpstream_prog
      (initJvmState [(0, .ext (.st st)), (1, .ext (.sv newUp)), (2, .ext (.uuid fresh))]) =
      some (.ext (.st (SessionValue.stepSetValueFromUpstream st newUp fresh))) := by
  rfl

end SessionValue.JvmVerification

#audit_jvm_equiv_axioms SessionValue.JvmVerification SessionValue.JvmBytecode

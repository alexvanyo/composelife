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

import Lean.Compiler.Kotlin
import SessionValue.Basic

open Lean.Compiler.Kotlin

namespace SessionValue

/--
The internal state of `SessionValueHolderImpl`.
-/
@[kotlin_class "data class SessionValueState"]
structure State (α : Type u) where
  upstreamSessionIdBeforeLocalSession : Uuid
  upstreamSessionValue : SessionValue α
  localSessionId : Uuid
  localSessionValue : Option (SessionValue α)
deriving DecidableEq, Repr, Inhabited

/--
The current exposed `sessionValue`.
Returns `localSessionValue` if present, otherwise `upstreamSessionValue`.
-/
@[export session_value_state_session_value, kotlin_member "SessionValueState" "public val" "sessionValue"]
def State.sessionValue (st : State α) : SessionValue α :=
  st.localSessionValue.getD st.upstreamSessionValue

/--
The current `LocalSessionInfo` calculated from `State`.
-/
@[export session_value_state_info, kotlin_member "SessionValueState" "public val" "info"]
def State.info (st : State α) : LocalSessionInfo :=
  match st.localSessionValue with
  | none =>
    LocalSessionInfo.inactive
      st.upstreamSessionValue.sessionId
      st.localSessionId
  | some lv =>
    LocalSessionInfo.active
      st.localSessionId
      (st.upstreamSessionValue.sessionId == lv.sessionId &&
       st.upstreamSessionValue.valueId == lv.valueId)
      st.upstreamSessionIdBeforeLocalSession

/--
Initial state constructor matching `rememberSessionValueHolder`:
`upstreamSessionIdBeforeLocalSession = upstreamSessionValue.sessionId`
`localSessionValue = none`
-/
def initialState (u0 : SessionValue α) (initLocalId : Uuid) : State α := {
  upstreamSessionIdBeforeLocalSession := u0.sessionId,
  upstreamSessionValue := u0,
  localSessionId := initLocalId,
  localSessionValue := none
}

/--
Transition `setValue`: updates local state immediately and returns the new state
together with the `(expected, newValue)` CAS update pair for upstream.
-/
@[export session_value_step_set_value, kotlin_member "SessionValueState" "public extension" "stepSetValue"]
def stepSetValue (st : State α) (v : α) (vid : Uuid) :
    State α × (SessionValue α × SessionValue α) :=
  let expected := st.sessionValue
  let newLocalVal : SessionValue α := {
    sessionId := st.localSessionId,
    valueId := vid,
    value := v
  }
  let st' := { st with localSessionValue := some newLocalVal }
  (st', (expected, newLocalVal))

/--
Transition `setValueFromUpstream`: synchronizes the state with an updated upstream value.
Handles:
- No-op when upstream value has not changed.
- Echo updates from our own local session (keeps local session active).
- Conflicting updates from foreign sessions (invalidates local session and resets to inactive).
- ID cycling when inactive.
-/
@[export session_value_step_set_value_from_upstream, kotlin_member "SessionValueState" "public extension" "stepSetValueFromUpstream"]
def stepSetValueFromUpstream (st : State α) (newUpstream : SessionValue α)
    (freshLocalSessionId : Uuid) : State α :=
  let hasSessionValueChanged : Bool :=
    newUpstream.sessionId != st.upstreamSessionValue.sessionId ||
    newUpstream.valueId != st.upstreamSessionValue.valueId
  if !hasSessionValueChanged then
    st
  else
    let isDifferentSession : Bool :=
      match st.localSessionValue with
      | some lv => newUpstream.sessionId != lv.sessionId
      | none => true
    let newLocalSessionId :=
      if isDifferentSession then freshLocalSessionId else st.localSessionId
    let newLocalSessionValue :=
      if isDifferentSession then none else st.localSessionValue
    let newUpstreamBefore :=
      if newLocalSessionId != newUpstream.sessionId then
        newUpstream.sessionId
      else
        st.upstreamSessionIdBeforeLocalSession
    {
      upstreamSessionIdBeforeLocalSession := newUpstreamBefore,
      upstreamSessionValue := newUpstream,
      localSessionId := newLocalSessionId,
      localSessionValue := newLocalSessionValue
    }

@[kotlin_file]
def stateMachineFileSpec : FileSpec := {
  imports := #[
    "import kotlin.uuid.Uuid"
  ]
  items := #[
    .topLevel
  ]
}

end SessionValue
